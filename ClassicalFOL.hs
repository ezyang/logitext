{-# LANGUAGE GADTs, EmptyDataDecls, KindSignatures, ExistentialQuantification, ScopedTypeVariables, DeriveDataTypeable #-}

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
import Control.Applicative
import Control.Exception
import Control.Monad
import Debug.Trace

import Text.XML.Light

-- Ltac is a flat language, but the proofs we want to create and modify
-- are trees.

-- The fact that we rely on Coq's naming to be deterministic REALLY SUCKS

type V = String
type PredV = String
type FunV = String

-- Sequent
data S = S [L] [L]
    deriving (Show, Eq)

-- We're not actually going to manipulate this; just use it for nice
-- printing.

-- Elements in the universe.  Distinguish between a constant and a
-- bound variable (probably not strictly necessary, but convenient)
data U = Fun FunV [U]
       | Var V
    deriving (Show, Eq)

instance CoqTerm U where
    toCoq (Fun f xs) = C.App (C.Atom f) (map toCoq xs)
    toCoq (Var x) = C.Atom x

    fromCoq = coqToU Set.empty where

-- a bit specialized, sorry
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
    deriving (Show, Eq)

instance CoqTerm L where
    -- TODO use associated types to allow for custom state
    -- that will be threaded through the fromCoq routine...

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
-- you now have an Proof (Q _) _, but we don't care about that for
-- now.)  It's unknown if it will work.  If it has been passed to Coq,
-- the third constructor is a Just containing the subgoals generated,
-- which depends on the value of Q.

data P = Goal S | forall i. Proof S (Q i) (Maybe (i P))
-- P S Q | Pending | Hole S

data Zero a = Zero
data One a = One a
data Two a = Two a a

data Q (i :: * -> *) where
    Exact      :: Int   -> Q Zero
    Cut        :: L     -> Q Two
    LConj      :: Int   -> Q One
    LDisj      :: Int   -> Q Two
    LImp       :: Int   -> Q Two
    LBot       :: Int   -> Q Zero
    LNot       :: Int   -> Q One
    LForall    :: Int -> V -> Q One
    LExists    :: Int   -> Q One
    LContract  :: Int   -> Q One
    LWeaken    :: Int   -> Q One
    RConj      :: Int   -> Q Two
    RDisj      :: Int   -> Q One
    RImp       :: Int   -> Q One
    RNot       :: Int   -> Q One
    RForall    :: Int   -> Q One
    RExists    :: Int -> V -> Q One
    RWeaken    :: Int   -> Q One
    RContract  :: Int   -> Q One

hyp n = "Hyp" ++ show n
con n = "Con" ++ show n

-- We need to do a rather special mechanism of feeding the proof to Coq,
-- because we need to find out what the intermediate proof state at
-- various steps looks like.

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

qn s = QName s Nothing Nothing

-- bottom on input we don't understand
-- Nothing on tactic failure
parseResponse :: [Content] -> Maybe S
parseResponse raw = do
    let fake = Element (qn "fake") [] raw Nothing
        isInterestingProp (C.Typed (C.Atom n) (C.Sort C.Prop)) | "Hyp" `isPrefixOf` n = True
        isInterestingProp _ = False
    -- showElement fake `trace` return ()
    when (isJust (findElement (qn "errorresponse") fake)) mzero
    -- yes, we're being partial here, but using ordering to
    -- ensure that the errors get sequenced correctly
    resp <- maybeError "pendingToHole: no response found" (findChild (qn "normalresponse") (Element (qn "fake") [] raw Nothing))
    mstatus <- findAttr (qn "status") resp
    -- done <- (== "no-more-subgoals") `traverse_` mstatus
    hyps <- filter isInterestingProp
          . rights
          . map (C.parseTerm . strContent)
          . findChildren (qn "hyp")
        <$> maybeError "pendingToHole: no hyps found" (findChild (qn "hyps") resp)
    goal <- eitherError . C.parseTerm . strContent =<< maybeError "pendingToHole: no goal found" (findChild (qn "goal") resp)
    return (S (map fromCoq hyps) (listifyDisj (fromCoq goal)))

refine :: P -> IO P
refine p@(Goal s)      = refine' s p
refine p@(Proof s _ _) = refine' s p

data UpdateFailure = UpdateFailure
    deriving (Typeable, Show)
instance Exception UpdateFailure

-- the S is kind of redundant but makes my life easier
refine' :: S -> P -> IO P
-- XXX not quite right
refine' s@(S [] cs) p = coqtop "ClassicalFOL" $ \f -> do
    -- XXX demand no errors
    mapM_ f [ "Section scratch."
            , "Parameter U : Set."
            -- XXX factor these constants out
            , "Variable z : U."
            , "Variable f g h : U -> U."
            , "Variable A B C : Prop."
            , "Variable P Q R : Prop."
            , "Set Printing All."
            ]
    currentState <- newIORef undefined
    let run tac = do
            r <- evaluate . parseResponse =<< f tac
            writeIORef currentState `traverse_` r
            -- it turns out the actual proof state isn't that useful;
            -- you conflate the /generated goals/ with /whether or
            -- not the tactic succeeded/. Arguably, we should
            -- rearchitect our interface around a different idea, but
            -- it turns out it's kind of convenient to delay verifying S.
            return (isJust r)
        readState = readIORef currentState
        checkState s = readState >>= \s' -> assert (s == s') (return ())
    r <- run ("Goal " ++ C.render (toCoq (disjList cs)) ++ ".")
    when (not r) $ error "refine: setting goal failed"
    checkState s

    let go1 :: Maybe (One P) -> Bool -> IO (Maybe (One P))
        go1 (Just (One _)) False = error "refine: inconsistent proof object"
        go1 Nothing False = throwIO UpdateFailure
        go1 (Just (One p)) True = Just . One <$> rec p
        go1 Nothing True = Just . One . Goal <$> readState
        rec p@(Goal s) = run "admit." >> return p
        rec p@(Proof s (RNot n) m) = run ("rNot " ++ con n ++ ".") >>= go1 m >>= return . Proof s (RNot n)

    rec p
-- XXX partial (not a particularly stringent requirement; you can get
-- around it with a few intros / tactic applications
refine' _ _ = error "pendingToHole: meta-implication must be phrased as implication"

main = let s = S [] [Pred "A" [], Not (Pred "A" [])]
       in refine (Proof s (RNot 1) (Just (One (Goal (S [Pred "A" []] [Pred "A" []])))))
