module ClassicalFOL where

import Ltac

-- Ltac is a flat language, but the proofs we want to create and modify
-- are trees.

-- The fact that we rely on Coq's naming to be deterministic REALLY SUCKS

type V = String

data S = S [L] [L]

data L = Atom V
       | Conj L L
       | Disj L L
       | Not L
       | Top
       | Bot
       -- mmm, more HOAS
       | Forall (V -> L)
       | Exists (V -> L)

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
