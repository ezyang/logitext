{-# LANGUAGE GADTs, EmptyDataDecls, KindSignatures, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, DeriveFunctor, NoMonomorphismRestriction, ViewPatterns #-}

module ClassicalFOL where

import qualified Coq as C
import Coq (CoqTerm(..))
import Ltac
import CoqTop
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Either
import Data.List
import Data.Foldable (traverse_)
import Data.IORef
import Data.Typeable
import Data.Word
import Data.Bits
import Data.Data
import qualified Data.ByteString.Lazy as Lazy
import Data.Aeson.Generic
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Debug.Trace
import Text.XML.Light

-- We rely on naming being deterministic, so that we can have 'pure'
-- proof data structures.  This is really not practical for real
-- proofs, where we really can't keep the all of the old proof states.

type V = String
type PredV = String
type FunV = String

-- Sequent
data S = S { hyps :: [L], cons :: [L] }
    deriving (Show, Eq, Data, Typeable)

{-
instance JSON S where
    readJSON (JSObject (fromJSObject -> o)) =
        case lookup "hyps" o of
        Just hyps ->
            case lookup "cons" o of
            Just cons -> S <$> readJSONs hyps <*> readJSONs cons
            _ -> Error "Could not read S"
        _ -> Error "Could not read S"
    readJSON _ = Error "Could not read S"
    showJSON (S hyps cons) = makeObj [("hyps", showJSONs hyps), ("cons", showJSONs cons)]
-}

-- Elements in the universe.  Distinguish between a constant and a
-- bound variable (probably not strictly necessary, but convenient)
data U = Fun FunV [U]
       | Var V
    deriving (Show, Eq, Data, Typeable)

instance CoqTerm U where
    toCoq (Fun f xs) = C.App (C.Atom f) (map toCoq xs)
    toCoq (Var x) = C.Atom x

    fromCoq = coqToU Set.empty where

-- XXX A bit specialized (not fromCoq because we need sets)
coqToU s (C.Atom n) | n `Set.member` s = Var n
               | otherwise = Fun n []
coqToU s (C.App (C.Atom n) us) = Fun n (map (coqToU s) us)
coqToU _ _ = error "U.fromCoq"

data L = Pred PredV [U] -- could be (Pred "A" [])
       | Conj L L
       | Disj L L
       | Imp L L
       | Not L
       | Top
       | Bot
       | Forall V L
       | Exists V L
    deriving (Show, Eq, Data, Typeable)

instance CoqTerm L where
    toCoq (Pred p []) = C.Atom p
    toCoq (Pred p xs) = C.App (C.Atom p) (map toCoq xs)
    toCoq (Conj a b) = C.App (C.Atom "and") [toCoq a, toCoq b]
    toCoq (Disj a b) = C.App (C.Atom "or") [toCoq a, toCoq b]
    toCoq (Imp a b) = C.Imp (toCoq a) (toCoq b)
    toCoq (Not a) = C.App (C.Atom "not") [toCoq a]
    toCoq Top = C.Atom "True"
    toCoq Bot = C.Atom "False"
    toCoq (Forall x a) = C.Forall [("x", C.Atom "U")] (toCoq a)
    toCoq (Exists x a) = C.App (C.Atom "@ex") [C.Atom "U", C.Fun [(x, C.Atom "U")] (toCoq a)]

    fromCoq = f Set.empty where
        f s (C.Forall [] t) = f s t
        f s (C.Forall ((n, C.Atom "U"):bs) t) = Forall n (f (Set.insert n s) (C.Forall bs t))
        f s (C.Fun _ _) = error "L.fromCoq Fun"
        f s (C.Typed t _) = f s t
        f s (C.Imp t t') = Imp (f s t) (f s t')
        f s (C.App (C.Atom "@ex") [C.Atom "U", C.Fun [(n, C.Atom "U")] t]) = Exists n (f (Set.insert n s) t)
        f s (C.App (C.Atom "@ex") _) = error "L.fromCoq App ex"
        f s (C.App (C.Atom "and") [t1, t2]) = Conj (f s t1) (f s t2)
        f s (C.App (C.Atom "and") _) = error "L.fromCoq App and"
        f s (C.App (C.Atom "or") [t1, t2]) = Disj (f s t1) (f s t2)
        f s (C.App (C.Atom "or") _) = error "L.fromCoq App or"
        f s (C.App (C.Atom "not") [t]) = Not (f s t)
        f s (C.App (C.Atom "not") _) = error "L.fromCoq App not"
        f s (C.App (C.Atom p) ts) = Pred p (map (coqToU s) ts)
        f s (C.App _ _) = error "L.fromCoq App"
        f s (C.Sort _) = error "L.fromCoq Sort"
        f s (C.Num _) = error "L.fromCoq Num"
        f s (C.Atom "True") = Top
        f s (C.Atom "False") = Bot
        f s (C.Atom n) = Pred n []

listifyDisj :: L -> [L]
listifyDisj Bot = []
listifyDisj (Disj t ts) = t : listifyDisj ts
listifyDisj _ = error "listifyDisj"

disjList :: [L] -> L
disjList [] = Bot
disjList (x:xs) = Disj x (disjList xs)

-- quickcheck: listifyDisj (disjList xs) == xs

-- Building up a proof tree is a multi-stage process.
--
-- You start off with a Goal S, where S is the thing you want to prove,
-- but not knowing what the right proof step is.
--
-- You might suggest some inference rule Q, in which case
-- you now have an Pending _ (Q _).  It's unknown if it will work, nor do
-- we know what the subgoals will be.
--
-- Finally, after passing it to Coq, we discover if it's successful
-- and replace it with a Proof term.

data P = Goal S | Pending S (Q Int) | Proof S (Q P)
    deriving (Show, Data, Typeable)

data Q a = Exact Int
         | Cut L a a
         | LConj Int a
         | LDisj Int a a
         | LImp Int a a
         | LBot Int
         | LNot Int a
         | LForall Int U a
         | LExists Int a
         | LContract Int a
         | LWeaken Int a
         | RConj Int a a
         | RDisj Int a
         | RImp Int a
         | RNot Int a
         | RForall Int a
         | RExists Int U a
         | RWeaken Int a
         | RContract Int a
    deriving (Functor, Show, Data, Typeable)

-- preorder traversal (does a full rebuild)
preorder fp fq a = tp a
  where
    -- XXX eep, only needs to be partial! Could use some GADTs here...
    tp p@(Goal _)       = fp p -- used for Goal -> Pending transition
    tp p@(Pending _ _)  = fp p -- used for Pending -> Proof transition
    tp p@(Proof s q)    = Proof s <$ fp p <*> tq q -- result discarded

    tq q@(Exact n)      = Exact n <$ fq q
    tq q@(Cut l x y)    = Cut l <$ fq q <*> tp x <*> tp y
    tq q@(LConj n x)    = LConj n <$ fq q <*> tp x
    tq q@(LDisj n x y)  = LDisj n <$ fq q <*> tp x <*> tp y
    tq q@(LImp n x y)   = LImp n <$ fq q <*> tp x <*> tp y
    tq q@(LBot n)       = LBot n <$ fq q
    tq q@(LNot n x)     = LNot n <$ fq q <*> tp x
    tq q@(LForall n v x) = LForall n v <$ fq q <*> tp x
    tq q@(LExists n x)  = LExists n <$ fq q <*> tp x
    tq q@(LContract n x) = LContract n <$ fq q <*> tp x
    tq q@(LWeaken n x)  = LWeaken n <$ fq q <*> tp x
    tq q@(RConj n x y)  = RConj n <$ fq q <*> tp x <*> tp y
    tq q@(RDisj n x)    = RDisj n <$ fq q <*> tp x
    tq q@(RImp n x)     = RImp n <$ fq q <*> tp x
    tq q@(RNot n x)     = RNot n <$ fq q <*> tp x
    tq q@(RForall n x)  = RForall n <$ fq q <*> tp x
    tq q@(RExists n v x) = RExists n v <$ fq q <*> tp x
    tq q@(RWeaken n x)  = RWeaken n <$ fq q <*> tp x
    tq q@(RContract n x) = RContract n <$ fq q <*> tp x

-- words are easier to pass around, and 32 proof steps ought to be enough
-- for anybody...
intToBits :: Word -> [Int]
intToBits 0 = [0]
intToBits 1 = [1]
intToBits n | n .&. 1 == 0 = 0 : intToBits (shiftR n 1)
            | otherwise    = 1 : intToBits (shiftR n 1)

update p is q = go p is where
    go (Goal s) [] = return (Pending s q)
    go _ [] = mzero
    go (Goal _) (_:_) = mzero
    go (Pending _ _) (_:_) = mzero
    go (Proof s q') (i:is) =
        let og (Cut l x y) 0 = Cut l <$> go x is <*> pure y
            og (Cut l x y) 1 = Cut l <$> pure x <*> go y is
            og (LConj n x) 0 = LConj n <$> go x is
            og (LDisj n x y) 0 = LDisj n <$> go x is <*> pure y
            og (LDisj n x y) 1 = LDisj n <$> pure x <*> go y is
            og (LImp n x y) 0 = LImp n <$> go x is <*> pure y
            og (LImp n x y) 1 = LImp n <$> pure x <*> go y is
            og (LNot n x) 0 = LNot n <$> go x is
            og (LForall n v x) 0 = LForall n v <$> go x is
            og (LExists n x) 0 = LExists n <$> go x is
            og (LContract n x) 0 = LContract n <$> go x is
            og (LWeaken n x) 0 = LWeaken n <$> go x is
            og (RConj n x y) 0 = RConj n <$> go x is <*> pure y
            og (RConj n x y) 1 = RConj n <$> pure x <*> go y is
            og (RDisj n x) 0 = RDisj n <$> go x is
            og (RImp n x) 0 = RImp n <$> go x is
            og (RNot n x) 0 = RNot n <$> go x is
            og (RForall n x) 0 = RForall n <$> go x is
            og (RExists n v x) 0 = RExists n v <$> go x is
            og (RWeaken n x) 0 = RWeaken n <$> go x is
            og (RContract n x) 0 = RContract n <$> go x is
            og _ _ = mzero
        in Proof s <$> og q' i

proofComplete a = isJust (preorder fp fq a)
  where fp p@(Goal _) = mzero
        fp p@(Pending _ _) = mzero
        fp p@(Proof _ _) = return undefined
        fq _ = return undefined

hyp n = "Hyp" ++ show n
con n = "Con" ++ show n

-- XXX a travesty against types all around the world... because I was too
-- lazy to actually write the case
qNum Exact{} = 0
qNum Cut{} = 2
qNum LConj{} = 1
qNum LDisj{} = 2
qNum LImp{} = 2
qNum LBot{} = 0
qNum LNot{} = 1
qNum LForall{} = 1
qNum LExists{} = 1
qNum LContract{} = 1
qNum LWeaken{} = 1
qNum RConj{} = 2
qNum RDisj{} = 1
qNum RImp{} = 1
qNum RNot{} = 1
qNum RForall{} = 1
qNum RExists{} = 1
qNum RWeaken{} = 1
qNum RContract{} = 1

qToTac (Exact n) = Tac "myExact" [hyp n]
qToTac (Cut l _ _) = Tac "myCut" [C.render (toCoq l)]
qToTac (LConj n _) = Tac "lConj" [hyp n]
qToTac (LDisj n _ _) = Tac "lDisj" [hyp n]
qToTac (LImp n _ _) = Tac "lImp" [hyp n]
qToTac (LBot n) = Tac "lBot" []
qToTac (LNot n _) = Tac "lNot" [hyp n]
qToTac (LForall n v _) = Tac "lForall" [hyp n, C.render (toCoq v)]
qToTac (LExists n _) = Tac "lExists" [hyp n]
qToTac (LContract n _) = Tac "lContract" [hyp n]
qToTac (LWeaken n _) = Tac "lWeaken" [hyp n]
qToTac (RConj n _ _) = Tac "rConj" [con n]
qToTac (RDisj n _) = Tac "rDisj" [con n]
qToTac (RImp n _) = Tac "rImp" [con n]
qToTac (RNot n _) = Tac "rNot" [con n]
qToTac (RForall n _) = Tac "rForall" [con n]
qToTac (RExists n v _) = Tac "rExists" [con n, C.render (toCoq v)]
qToTac (RWeaken n _) = Tac "rWeaken" [con n]
qToTac (RContract n _) = Tac "rContract" [con n]

-- We need to do a rather special mechanism of feeding the proof to Coq,
-- because we need to find out what the intermediate proof state at
-- various steps looks like.  (Also, we'd kind of like to save work...)

-- using error, not fail!  fail will have the wrong semantics
-- when we're using Maybe
maybeError s m = maybe (error s) return m
eitherError = either (error . show) return

-- NOTE Tactic failure may be from a built in (i.e. no clauses for
-- match) or from an explicit fail, which can have a string resulting
-- in "Error: Tactic failure: foo."  We don't appear to have any
-- need for sophisticated failure matching yet, and the errors are
-- in general kind of useless, but maybe it will be useful later.
-- Note that we have an opportunity for *unsound* error generation:
-- "if there is an error, this message might be useful" (kind of like
-- how humans, faced with a fact that is in fact false, can still make
-- up plausible excuses.)

data CoqError = TacticFailure | NoMoreSubgoals
    deriving (Show)

-- but bottom on input we don't understand
parseResponse :: [Content] -> Either CoqError S
parseResponse raw = do
    let fake = Element (qn "fake") [] raw Nothing
        extractHyp (C.Typed (C.Atom _) (C.App (C.Atom "Hyp") [l])) = Just l
        extractHyp _ = Nothing
        qn s = QName s Nothing Nothing
    -- showElement fake `trace` return ()
    when (isJust (findElement (qn "errorresponse") fake)) (Left TacticFailure)
    -- yes, we're being partial here, but using ordering to
    -- ensure that the errors get sequenced correctly
    resp <- maybeError "pendingToHole: no response found" (findChild (qn "normalresponse") (Element (qn "fake") [] raw Nothing))
    (\s -> when (s == "no-more-subgoals") (Left NoMoreSubgoals)) `traverse_` findAttr (qn "status") resp
    hyps <- mapMaybe extractHyp
          . rights
          . map (C.parseTerm . strContent)
          . findChildren (qn "hyp")
        <$> maybeError "pendingToHole: no hyps found" (findChild (qn "hyps") resp)
    goal <- eitherError . C.parseTerm . strContent =<< maybeError "pendingToHole: no goal found" (findChild (qn "goal") resp)
    return (S (map fromCoq hyps) (listifyDisj (fromCoq goal)))

refine :: P -> IO P
refine p@(Goal s)      = refine' s p
refine p@(Pending s _) = refine' s p
refine p@(Proof s _)   = refine' s p

data UpdateFailure = UpdateFailure
    deriving (Typeable, Show)
instance Exception UpdateFailure

-- the S is kind of redundant but makes my life easier
refine' :: S -> P -> IO P
-- XXX not quite right
refine' s@(S [] cs) p = coqtop "ClassicalFOL" $ \f -> do
    -- XXX demand no errors
    mapM_ f [ "Section scratch"
            , "Parameter U : Set"
            -- XXX factor these constants out
            , "Variable z : U"
            , "Variable f g h : U -> U"
            , "Variable A B C : Prop"
            , "Variable P Q R : Prop"
            , "Set Printing All"
            ]
    -- despite being horrible mutation, this plays an important
    -- synchronizing role for us; it lets us make sure that "what we
    -- see" is what we expect; also, immediately after we run a tactic
    -- is not /quite/ the right place to check the result
    currentState <- newIORef Nothing
    let run tac = do
            -- putStrLn tac
            r <- evaluate . parseResponse =<< f tac
            case r of
                Right x -> writeIORef currentState (Just x) >> return True
                Left TacticFailure -> return False
                Left NoMoreSubgoals -> writeIORef currentState Nothing >> return True
        readState = readIORef currentState
        checkState s = readState >>= \s' -> assert (Just s == s') (return ())
    r <- run ("Goal " ++ C.render (toCoq (disjList cs)))
    when (not r) $ error "refine: setting goal failed"
    let fp p@(Goal s) = checkState s >> return p
        -- TODO also check if change in number of subgoals is correct
        fp p@(Pending s q) = do
            checkState s
            run (show (qToTac q)) >>= (`unless` throwIO UpdateFailure)
            gs <- replicateM (qNum q) (fromJust <$> readState <* (run "admit" >>= (`unless` error "refine: could not admit")))
            return (Proof s (fmap (Goal . (gs !!)) q))
        fp (Proof s _) = checkState s >> return undefined
        fq q = run (show (qToTac q)) >>= (`unless` error "refine: inconsistent proof state")
    preorder fp fq p

-- XXX partial (not a particularly stringent requirement; you can get
-- around it with a few intros / tactic applications
refine' _ _ = error "pendingToHole: meta-implication must be phrased as implication"

refineString :: Lazy.ByteString -> IO (Maybe Lazy.ByteString)
refineString s =
    case decode s of
    Just a -> Just . encode <$> refine a
    _ -> return Nothing

main = do
    let s = S [] [Pred "A" [], Not (Pred "A" [])]
    -- XXX actually kinda slow...
    {-
    print =<< refine (Goal s)
    print =<< refine (Pending s (RNot 1 0))
    print =<< refine (Proof s (RNot 1 (Goal (S [Pred "A" []] [Pred "A" []]))))
    print =<< refine (Proof s (RNot 1 (Pending (S [Pred "A" []] [Pred "A" []]) (Exact 0))))
    -}
    print . encode =<< refine (Proof s (RNot 1 (Proof (S [Pred "A" []] [Pred "A" []]) (Exact 0))))
