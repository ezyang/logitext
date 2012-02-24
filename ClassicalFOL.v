Require Import List.
Require Import Classical.

(* a convenient representation for interpreting sequents; this is how we'll receive inputs
   from the external system. Converting backwards is nontrivial, so we'll just parse
   it out. *)
Inductive deduction :=
  | dd : list Prop -> list Prop -> deduction.

Notation "P |= Q" := (dd P Q) (at level 90).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition denote (s : deduction) : Prop :=
  match s with
    | dd ass con => fold_right and True ass -> fold_right or False con
  end.
(* The trailing false acts as a sort of bookend, which helps keep us
from getting confused. But this representation will be kind of annoying
to manipulate *)

Lemma contrapositive : forall (A B : Prop), (~ B -> ~ A) <-> (A -> B).
  intros; destruct (classic B); tauto.
Qed.

(* Slightly opaque definition to help us keep track of hypotheses
versus parametric values *)
Definition Hyp (x : Prop) := x.

Ltac conjExplode H :=
  repeat (let h := fresh in destruct H as [ h H ]; let x := type of h in change (Hyp x) in h); destruct H.
Ltac negDisjExplode H :=
  repeat (let h := fresh in apply not_or_and in H; destruct H as [ h H ]; let x := type of h in change (Hyp x) in h); clear H. (* clear, because destruct does the wrong thing *)
Ltac unwrap := cbv; intro H; conjExplode H.

(* sequent calculus rules *)

Ltac myExact := fail.
Ltac myCut := fail.

Ltac negImp H :=
  match type of H with Hyp (~ (_ (* H1 *) -> _ (* H2 *))) =>
    unfold Hyp in H; apply imply_to_and in H;
    (* H : H1 /\ ~ H2 *)
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    (* Want to move H1 to the bottom (as a negative); keep H2 up top *)
    match goal with
      [ |- ?G ] =>
        let h := fresh in
        let T1 := type of H1 in
        assert (h : ~ T1 \/ G); [|
          let nH1 := fresh in let G' := fresh in
          destruct h as [ nH1 | G' ]; [ contradict H1; exact nH1 | exact G' ]
        ]
    end;
    clear H1;
    let T2 := type of H2 in change (Hyp T2) in H2;
    apply not_and_or
  end.

Ltac rollupPositive H :=
  repeat match goal with
           | [ H' : Hyp ?P |- _ ] => revert H' end;
  assert (H : True) by trivial;
  repeat match goal with
           | [ |- _ -> _ ] =>
             let h := fresh in intro h;
             let ht := type of h in
             let Ht := type of H in
             let g := fresh in
             assert (ht /\ Ht) as g; [constructor; assumption |];
             clear H; clear h; rename g into H
         end;
  unfold Hyp in H;
  revert H.

Ltac posneg :=
  let H := fresh in
  rollupPositive H;
  apply contrapositive;
  intro H;
  negDisjExplode H.

(* refactor this with rollupPositive *)
Ltac rollupNegative H :=
  repeat match goal with
           | [ H' : Hyp ?P |- _ ] => revert H' end;
  assert (H : ~ False) by tauto;
  repeat match goal with
           | [ |- _ -> _ ] =>
             let h := fresh in intro h;
             let ht := type of h in
             let Ht := type of H in
             let g := fresh in
             assert (ht /\ Ht) as g; [constructor; assumption |];
             clear H; clear h; rename g into H;
             apply and_not_or in H
         end; revert H.

Ltac negpos :=
  let H := fresh in
  rollupNegative H;
  apply <- contrapositive;
  intro H;
  conjExplode H.

Ltac canonicalize := posneg; negpos.

(* alternatively, duplicate the hypothesis and only provide fst and snd projection *)
Ltac lConj H :=
  match type of H with Hyp (_ /\ _) =>
    let h1 := fresh in let h2 := fresh in unfold Hyp in H; destruct H as [h1 h2];
    let t1 := type of h1 in let t2 := type of h2 in change (Hyp t1) in h1; change (Hyp t2) in h2
  end; canonicalize.
Ltac lDisj H := fail.
Ltac lImp H := fail.
(*
  match type of H with Hyp (?P -> ?Q) =>
    match goal with [ |- ?G ] =>
      assert P; *)
Ltac lBot H := fail.
Ltac lForall H t := fail.
Ltac lExists H := fail.
Ltac lDup H := fail.

Ltac rConj := fail.
Ltac rDisjL := fail.
Ltac rDisjR := fail.
Ltac rImp H := posneg; negImp H; negpos.
Ltac rForall := fail.
Ltac rExists t := fail.
Ltac rDup := fail.

Section universe.

Variable U : Set.
Variable z : U. (* non-empty domain *)
Variables A B C : Prop. (* some convenient things to instantiate with *)

(* an example *)
Goal denote ( [ True; C; C /\ C ] |= [ ((A -> B) -> A) -> A; False ] ).
  unwrap.
  lConj H2.
  rImp H0.
Abort.

End Section.