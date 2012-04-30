{-# LANGUAGE GADTs, EmptyDataDecls, KindSignatures, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable, DeriveFunctor, NoMonomorphismRestriction, ViewPatterns #-}

module ClassicalFOL where

import qualified Data.Set as Set
import Data.Maybe
import Data.Either
import Data.Foldable (traverse_)
import Data.IORef
import Data.Typeable
import Data.Data
import qualified Data.ByteString.Lazy as Lazy
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Concurrent.MVar
import System.IO.Unsafe
import Text.XML.Light
import Data.Aeson.Types (Result(..))
import Data.Aeson (json')
import qualified Data.Aeson.Encode as E
import qualified Data.Attoparsec.Lazy as L

import qualified Coq as C
import Coq (CoqTerm(..))
import Ltac
import CoqTop
import JSONGeneric

errorModule s = error ("ClassicalFOL: " ++ s)

-- We rely on naming being deterministic, so that we can have 'pure'
-- proof data structures.  This is really not practical for real
-- proofs, where we really can't keep the all of the old proof states.

type V = String
type PredV = String
type FunV = String

-- Sequent
data S = S { hyps :: [L], cons :: [L] }
    deriving (Show, Eq, Data, Typeable)

-- Elements in the universe.  Distinguish between a constant and a
-- bound variable (probably not strictly necessary, but convenient)
data U = Fun FunV [U]
       | Var V
    deriving (Show, Eq, Data, Typeable)

instance CoqTerm U where
    toCoq (Fun f xs) = C.App (C.Atom f) (map toCoq xs)
    toCoq (Var x) = C.Atom x
    fromCoq = coqToU Set.empty

-- (see CoqTerm XXX in Coq for clarification)
coqToU s (C.Atom n) | n `Set.member` s = Var n
                    | otherwise = Fun n []
coqToU s (C.App (C.Atom n) us) = Fun n (map (coqToU s) us)
coqToU _ _ = errorModule "coqToU"

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
    toCoq (Forall x a) = C.Forall [(x, C.Atom "U")] (toCoq a)
    toCoq (Exists x a) = C.App (C.Atom "@ex") [C.Atom "U", C.Fun [(x, C.Atom "U")] (toCoq a)]

    fromCoq = f Set.empty where
        f s (C.Forall [] t) = f s t
        f s (C.Forall ((n, C.Atom "U"):bs) t) = Forall n (f (Set.insert n s) (C.Forall bs t))
        f _ (C.Forall _ _) = errorModule "L.fromCoq Forall"
        f _ (C.Fun _ _) = errorModule "L.fromCoq Fun"
        f s (C.Typed t _) = f s t
        f s (C.Imp t t') = Imp (f s t) (f s t')
        f s (C.App (C.Atom "@ex") [C.Atom "U", C.Fun [(n, C.Atom "U")] t]) = Exists n (f (Set.insert n s) t)
        f _ (C.App (C.Atom "@ex") _) = errorModule "L.fromCoq App ex"
        f s (C.App (C.Atom "and") [t1, t2]) = Conj (f s t1) (f s t2)
        f _ (C.App (C.Atom "and") _) = errorModule "L.fromCoq App and"
        f s (C.App (C.Atom "or") [t1, t2]) = Disj (f s t1) (f s t2)
        f _ (C.App (C.Atom "or") _) = errorModule "L.fromCoq App or"
        f s (C.App (C.Atom "not") [t]) = Not (f s t)
        f _ (C.App (C.Atom "not") _) = errorModule "L.fromCoq App not"
        f s (C.App (C.Atom p) ts) = Pred p (map (coqToU s) ts)
        f _ (C.App _ _) = errorModule "L.fromCoq App"
        f _ (C.Sort _) = errorModule "L.fromCoq Sort"
        f _ (C.Num _) = errorModule "L.fromCoq Num"
        f _ (C.Atom "True") = Top
        f _ (C.Atom "False") = Bot
        f _ (C.Atom n) = Pred n []

listifyDisj :: L -> [L]
listifyDisj Bot = []
listifyDisj (Disj t ts) = t : listifyDisj ts
listifyDisj _ = errorModule "listifyDisj"

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
-- we know what the subgoals will be.  Note that we abuse the polymorphism
-- of tactic to help mapping from Q Int -> Q P; all of the entries
-- of a pending tactic enumerate up from 0; so you can do a fmap in
-- order to instantiate P after you pass it to Coq.
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

-- preorder traversal for side effects (does a full rebuild)
preorder :: Applicative f => (P -> f P) -> (Q P -> f ()) -> P -> f P
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

proofComplete a = isJust (preorder fp fq a)
  where fp (Goal _) = Nothing
        fp (Pending _ _) = Nothing
        fp p@(Proof _ _) = Just p
        fq _ = Just ()

hyp n = "Hyp" ++ show n
con n = "Con" ++ show n

qToTac (Exact n) = Tac "myExact" [hyp n]
qToTac (Cut l _ _) = Tac "myCut" [C.render (toCoq l)]
qToTac (LConj n _) = Tac "lConj" [hyp n]
qToTac (LDisj n _ _) = Tac "lDisj" [hyp n]
qToTac (LImp n _ _) = Tac "lImp" [hyp n]
qToTac (LBot _) = Tac "lBot" [] -- XXX huh, kind of a weird tactic
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
maybeError s m = maybe (errorModule s) return m
eitherError = either (errorModule . show) return

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
    resp <- maybeError "parseResponse: no response found" (findChild (qn "normalresponse") (Element (qn "fake") [] raw Nothing))
    (\s -> when (s == "no-more-subgoals") (Left NoMoreSubgoals)) `traverse_` findAttr (qn "status") resp
    hypList <- mapMaybe extractHyp
             . rights
             . map (C.parseTerm . strContent)
             . findChildren (qn "hyp")
        <$> maybeError "parseResponse: no hyps found" (findChild (qn "hyps") resp)
    goal <- eitherError . C.parseTerm . strContent =<< maybeError "parseResponse: no goal found" (findChild (qn "goal") resp)
    return (S (map fromCoq hypList) (listifyDisj (fromCoq goal)))

data UpdateFailure = UpdateFailure
    deriving (Typeable, Show)
instance Exception UpdateFailure

-- XXX leaky leak leak.  Also, it's a bottleneck.  (Try using a resource
-- pool or something).  Also, we can make this more robust by rebooting
-- Coq if invariants are violated.
{-# NOINLINE theCoq #-}
theCoq = unsafePerformIO $ do
    (f, _) <- coqtopRaw "ClassicalFOL"
    mapM_ f
        [ "Section scratch"
        , "Parameter U : Set"
        -- XXX factor these constants out
        , "Variable z : U"
        , "Variable f g h : U -> U"
        , "Variable A B C : Prop"
        , "Variable P Q R : Prop"
        , "Set Printing All"
        , "Set Default Timeout 1" -- should be more than enough! no proof search see?
        , "Set Undo 0" -- not gonna use it
        ]
    newMVar f

start :: String -> IO P
start g = do
    goal <- eitherError $ C.parseTerm g
    return (Goal (S [] [fromCoq goal]))

refine :: P -> IO P
refine p@(Goal s)      = refine' s p
refine p@(Pending s _) = refine' s p
refine p@(Proof s _)   = refine' s p

-- the S is kind of redundant but makes my life easier
refine' :: S -> P -> IO P
refine' (S [] cs) pTop = withMVar theCoq $ \f -> do
    -- XXX demand no errors
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
    when (not r) $ errorModule "refine: setting goal failed" -- we're kind of screwed
    let fp p@(Goal s) = checkState s >> return p
        -- TODO also check if change in number of subgoals is correct
        fp (Pending s q) = do
            checkState s
            run (show (qToTac q)) >>= (`unless` throwIO UpdateFailure)
            -- XXX This is a /terrifying/ abuse of functoriality,
            let qNum Exact{} = 0
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
            gs <- replicateM (qNum q) $ do
                goal <- maybeError "refine: currentState empty" =<< readState
                run "admit" >>= (`unless` errorModule "refine: could not admit")
                return goal
            let index [] _ = errorModule "refine/index: out of bound index"
                index (x:xs) n | n < 0 = errorModule "refine/index: negative index"
                               | n == 0 = x
                               | otherwise = index xs (n-1)
            return (Proof s (fmap (Goal . (gs `index`)) q))
        fp (Proof s _) = checkState s >> return undefined
        fq q = run (show (qToTac q)) >>= (`unless` errorModule "refine: inconsistent proof state")
    preorder fp fq pTop `finally` f "Abort All"

-- XXX partial (not a particularly stringent requirement; you can get
-- around it with a few intros / tactic applications
refine' _ _ = errorModule "refine: meta-implication must be phrased as implication"

startString :: String -> IO Lazy.ByteString
startString s = E.encode . toJSON <$> start s

refineString :: Lazy.ByteString -> IO (Maybe Lazy.ByteString)
refineString s =
    case L.parse json' s of
        L.Done _ v -> case fromJSON v of
            -- XXX refine errors should be turned into nothing
            Success a -> Just . E.encode . toJSON <$> refine a
            _ -> return Nothing
        _ -> return Nothing
