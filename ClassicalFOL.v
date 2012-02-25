Require Import List.
Require Import Classical.

(* a convenient representation for interpreting sequents; this is how we'll receive inputs
   from the external system. *)
Inductive deduction :=
  | dd : list Prop -> list Prop -> deduction.

Notation "P |= Q" := (dd P Q) (at level 90).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition denote (s : deduction) : Prop :=
  match s with
    | dd hyp con => fold_right and True hyp -> fold_right or False con
  end.

Lemma contrapositive : forall (A B : Prop), (~ B -> ~ A) <-> (A -> B).
  intros; destruct (classic B); tauto. (* a little sloppy; the reverse direction is intuitionistically valid *)
Qed.

(* Slightly opaque definition to help us keep track of hypotheses
versus parametric values and temporary hypotheses *)
Definition Hyp (x : Prop) := x.
Definition Con (x : Prop) := x. (* not used by anyone; adding this identifier makes numbering start from 0 *)

(* Mark a hypothesis as user hypothesis, for easy tracking later *)
Ltac wrap H := let T := type of H in change (Hyp T) in H.
Ltac unwrap H := unfold Hyp in H.

(* Take a single hypothesis which is a list of conjunctions or a negated list of
   disjunctions and split them all into separate hypotheses.  We assume that the
   LAST hypothesis is True or some equivalent form (so it can be safely cleared.) *)
Ltac explode myfresh H tac :=
  repeat (let h := myfresh idtac in tac; destruct H as [ h H ]; wrap h);
  match type of H with True => clear H | ~ False => clear H end.
Ltac conjExplode H := explode ltac:(fun _ => fresh "Hyp") H ltac:idtac.
Ltac negDisjExplode H := explode ltac:(fun _ => fresh "Con") H ltac:(apply not_or_and in H).

(* Get started *)
Ltac sequent := simpl; let H := fresh in intro H; conjExplode H.

(* Heavy machinery for handling right-side rules *)

Ltac rollup H tac := (* examples for posneg case *)
  (* H : True, Hyp0 : Hyp ?T0, Hyp1 : Hyp ?T1 |- ?G *)
  repeat match goal with
           | [ H' : Hyp ?T' |- _ ] =>
             let T := type of H in
             let G := fresh in
             assert (T' /\ T) as G by (constructor; assumption);
             clear H'; clear H; rename G into H; tac
         end;
  (* H : ?T0 /\ ?T1 /\ True |- ?G *)
  revert H.
  (* |- ?T0 /\ ?T1 /\ True -> ?G *)

Ltac posneg :=
  (* Hyp0 : Hyp ?T0, Hyp1 : Hyp ?T1 |- ?C0 \/ ?C1 \/ False *)
  let H := fresh "tmp" in
  assert True as H by trivial;
  rollup H ltac:idtac;
  (* |- ?T0 /\ ?T1 /\ True -> ?C0 \/ ?C1 \/ False *)
  apply -> contrapositive;
  (* |- ~ (?C0 \/ ?C1 \/ False) -> ~ (?T0 /\ ?T1 /\ True) *)
  intro H; negDisjExplode H.
  (* Con0 : Hyp (~ ?C0), Con1 : Hyp (~ ?C1) |- ~ (?T0 /\ ?T1 /\ True) *)

Ltac negpos :=
  (* Con0 : Hyp (~ ?C0), Con1 : Hyp (~ ?C1) |- ~ (?T0 /\ ?T1 /\ True) *)
  let H := fresh "tmp" in
  assert (~ False) as H by tauto;
  rollup H ltac:(apply and_not_or in H);
  (* |- ~ (?C0 \/ ?C1 \/ False) -> ~ (?T0 /\ ?T1 /\ True) *)
  apply <- contrapositive;
  (* |- (?T0 /\ ?T1 /\ True) -> (?C0 \/ ?C1 \/ False) *)
  intro H; conjExplode H.
  (* Hyp0 : Hyp ?T0, Hyp1 : Hyp ?T1 |- ?C0 \/ ?C1 \/ False *)

Ltac canonicalize := posneg; negpos.

(* Heavy machinery that will be used to implement right-side rules *)

Ltac negImp H :=
  match type of H with Hyp (~ (_ (* H1 *) -> _ (* H2 *))) =>
    unwrap H; apply imply_to_and in H;
    (* H : H1 /\ ~ H2 *)
    let H1 := fresh in let H2 := fresh in
    destruct H as [H1 H2];
    (* Want to move H1 to the bottom (since it is positive); keep H2 up top *)
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
    wrap H2;
    apply not_and_or
  end.

Ltac negDisj H :=
  match type of H with Hyp (~ (_ (* H1 *) \/ _ (* H2 *))) =>
    unwrap H; apply not_or_and in H;
    (* H : ~ H1 /\ ~ H2 *)
    let H1 := fresh in let H2 := fresh in
    destruct H as [ H1 H2 ];
    wrap H1; wrap H2
  end.

(* actual user visible tactics *)

Ltac myExact H :=
  solve [unwrap H; repeat match goal with [ |- ?P \/ ?Q ] => try (solve [left; exact H]); right end].
Ltac myCut := fail.

(* alternatively, duplicate the hypothesis and only provide fst and snd projection *)
Ltac lConj H :=
  match type of H with Hyp (_ /\ _) =>
    let h1 := fresh in let h2 := fresh in unwrap H; destruct H as [h1 h2];
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

Ltac rWrap tac H := posneg; tac H; negpos; posneg; negpos.

Ltac rConj H := fail.
(* Alternatively, commit to a disjunction *)
Ltac rDisj H := rWrap negDisj H.
Ltac rImp H := rWrap negImp H.
Ltac rForall H := fail.
Ltac rExists H t := fail.
Ltac rDup H := fail.

Section universe.

Parameter U : Set.
Variable z : U. (* non-empty domain *)
Variables A B C : Prop. (* some convenient things to instantiate with *)

(* an example *)
Goal denote ( [ True; C /\ C ] |= [ False; False; False; ((A -> B) -> A) -> A ] ).
  sequent.
    lConj Hyp1.
    rImp Con3.
Abort.

Goal denote ( nil |= [ ((A -> B) -> A) -> A ] ).
  sequent.
    rImp Con0.
    destruct (classic (A -> B)). admit.
Abort.

Goal denote ( nil |= [ A \/ (A -> False) ] ).
  sequent.
    rDisj Con0.
    rImp Con1.
    myExact Hyp0.
Qed.

End universe.