Require Import List.

(* a non-empty universe; we shall not concern ourselves with matters of denotation *)
Parameter U : Set.

Parameter a b c : U.
Parameter f : U -> U.
Parameter P : U -> Prop.
Parameter A B C : Prop.

(* a convenient representation for interpreting sequents; this is how we'll receive inputs
   from the external system. Converting backwards is nontrivial, so we'll just parse
   it out. *)
Inductive deduction :=
  | dd : list Prop -> Prop -> deduction.

Notation "P |= Q" := (dd P Q) (at level 90).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition denote (s : deduction) : Prop :=
  match s with
    | dd ass con => fold_right and True ass -> con
  end.

(* utilities for manipulating sequents. We take the convention that
all names generated must have the name Hyp in them, although we
might be able to relax this convention because our contexts will
have "no pollution" *)
Ltac myfresh := fresh "Hyp".
Ltac introf := let h := myfresh in intro h.
Ltac explode H :=
  repeat (let h := myfresh in destruct H as [ h H ]).
Ltac unwrap := cbv; intro H; explode H.

(* sequent calculus rules *)

Ltac dCharge H := exact H.

(* alternatively, duplicate the hypothesis and only provide fst and snd projection *)
Ltac lConj H := let h1 := myfresh in let h2 := myfresh in destruct H as [ h1 h2 ].
Ltac lDisj H := destruct H as [ H | H ].
Ltac lImp H := match type of H with ?P -> ?Q => assert P; [|clear H] end.
Ltac lBot H := destruct H.
Ltac lForall H t := specialize (H t).
Ltac lExists H := destruct H.

(* parameter not necessary here because we're in intuitionistic logic *)
Ltac rConj := constructor.
Ltac rDisjL := left.
Ltac rDisjR := right.
Ltac rImp := introf.
Ltac rForall := intro. (* fix me *)
Ltac rExists t := exists t.

Ltac dCut H := (* cut H; [introf|] // wrong order *)
  let h := myfresh in assert (h : H).

(* convenience *)
Ltac dup H := let x := type of H in dCut x; [exact H|].

(* an example *)
Goal denote ([ forall a, P a ] |= (exists a, P a) ).
  unwrap.
    dCut (forall a, P a).
    exact Hyp.
    lForall Hyp a.
    rExists a.
    exact Hyp.
    lExists Hyp.
    lForall Hyp a.
    exact Hyp.
    dCut False.
    generalize Hyp.
    elim Hyp. change (denote ([True /\ True; False \/ False; A] |= False)).
Qed.