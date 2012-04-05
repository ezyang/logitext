module ClassicalFOL where

import qualified Coq
import qualified Ltac
import Data.Set (Set)
import qualified Data.Set as Set

-- Ltac is a flat language, but the proofs we want to create and modify
-- are trees.

-- The fact that we rely on Coq's naming to be deterministic REALLY SUCKS

type V = String
type PredV = String
type FunV = String

-- Sequent
data S = S [L] [L]

-- We're not actually going to manipulate this; just use it for nice
-- printing.

-- Elements in the universe.  Distinguish between a constant and a
-- bound variable (probably not strictly necessary, but convenient)
data U = Fun FunV [U]
       | Var V
    deriving (Show)

data L = Pred PredV [U] -- could be (Pred "A" [])
       | Conj L L
       | Disj L L
       | Imp L L
       | Not L
       | Top
       | Bot
       | Forall V L
       | Exists V L
    deriving (Show)

-- arguably should maintain a set of bound variables, so we can pass it
-- to coqToU
coqToL :: Set V -> Coq.Term -> L
coqToL s (Coq.Forall [] t) = coqToL s t
coqToL s (Coq.Forall ((n, Coq.Atom "U"):bs) t) = Forall n (coqToL (Set.insert n s) (Coq.Forall bs t))
coqToL s (Coq.Fun _ _) = error "coqToL: Fun"
coqToL s (Coq.Typed t _) = coqToL s t
coqToL s (Coq.Imp t t') = Imp (coqToL s t) (coqToL s t')
coqToL s (Coq.App (Coq.Atom "ex") [Coq.Atom "U", Coq.Fun [(n, Coq.Atom "U")] t]) = Exists n (coqToL (Set.insert n s) t)
coqToL s (Coq.App (Coq.Atom "ex") _) = error "coqToL: App ex"
coqToL s (Coq.App (Coq.Atom "and") [t1, t2]) = Conj (coqToL s t1) (coqToL s t2)
coqToL s (Coq.App (Coq.Atom "and") _) = error "coqToL: App and"
coqToL s (Coq.App (Coq.Atom "or") [t1, t2]) = Disj (coqToL s t1) (coqToL s t2)
coqToL s (Coq.App (Coq.Atom "or") _) = error "coqToL: App or"
coqToL s (Coq.App (Coq.Atom "not") [t]) = Not (coqToL s t)
coqToL s (Coq.App (Coq.Atom "not") _) = error "coqToL: App not"
coqToL s (Coq.App (Coq.Atom p) ts) = Pred p (map (coqToU s) ts)
coqToL s (Coq.App _ _) = error "coqToL: App"
coqToL s (Coq.Sort _) = error "coqToL: Sort"
coqToL s (Coq.Num _) = error "coqToL: Num"
coqToL s (Coq.Atom "True") = Top
coqToL s (Coq.Atom "False") = Bot
coqToL s (Coq.Atom n) = Pred n []

coqToU :: Set V -> Coq.Term -> U
coqToU s (Coq.Atom n) | n `Set.member` s = Var n
                      | otherwise = Fun n []
coqToU s (Coq.App (Coq.Atom f) us) = Fun f (map (coqToU s) us)
coqToU _ _ = error "coqToU"

listifyDisj :: L -> [L]
listifyDisj Bot = []
listifyDisj (Disj t ts) = t : listifyDisj ts
listifyDisj _ = error "listifyDisj"

data P = P S Q

data Q = Exact      Int
       | Cut        L P P
       | LConj      Int P
       | LDisj      Int P P
       | LImp       Int P P
       | LBot       Int
       | LNot       Int P
       | LForall    Int V P
       | LExists    Int P
       | LContract  Int P
       | LWeaken    Int P
       | RConj      Int P P
       | RDisj      Int P
       | RImp       Int P
       | RNot       Int P
       | RForall    Int P
       | RExists    Int V P
       | RWeaken    Int P
       | RContract  Int P
