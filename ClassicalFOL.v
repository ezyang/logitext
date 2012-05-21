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
Ltac sequent := simpl denote; let H := fresh in intro H; conjExplode H.

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

(* These tactics help you get rid of negative hypotheses by transforming
   them into cases of the disjunction. *)

(* XXX don't really know how to refactor dropNeg and dropPos into one function *)
Ltac dropNeg nH :=
  (* H : ~ ?T |- ?G *)
  match type of nH with ~ ?T =>
  match goal with [ |- ?TG ] =>
    let x := fresh in
    cut (T \/ TG);
    [ let H := fresh in let G := fresh in
      destruct 1 as [ H | G ]; [ exfalso; apply nH; trivial | exact G ]
    |]
  end end; clear nH.
  (* |- ?P \/ ?G *)

Ltac dropPos H :=
  (* H : ?T |- ~ ?G *)
  let T := type of H in
  match goal with [ |- ~ ?TG ] =>
    cut (~ T \/ ~ TG);
    [ let nH := fresh in let nG := fresh in
      destruct 1 as [ nH | nG ]; [ contradict nH; exact H | exact nG ]
    |]
  end;
  clear H;
  (* |- ~ ?T \/ ~ ?G *)
  apply not_and_or.
  (* |- ~ (?T /\ ?G) *)

(* actual user visible tactics *)

Ltac myCut T :=
  match goal with [ |- ?G ] =>
    cut (T \/ G); [ let G := fresh in intro G; destruct G as [G|G]; [wrap G|exact G] | ]
  end.

(* alternatively, duplicate the hypothesis and only provide fst and snd projection *)
(* ordering is a bit sensitive here. lConj generates a bunch of new labels, so
   they all get dumped at the beginning of the hypothesis context after a canonicalize;
   but lDisj doesn't increase in size so no reordering happens. It's unclear what's
   preferable. *)
Ltac lExact H :=
  solve [unwrap H; repeat match goal with [ |- ?P \/ ?Q ] => try (solve [left; exact H]); right end].
Ltac lConj H :=
  match type of H with Hyp (_ /\ _) =>
    let H1 := fresh in let H2 := fresh in
    unwrap H; destruct H as [H1 H2]; wrap H1; wrap H2
  end; canonicalize.
Ltac lDisj H :=
  match type of H with Hyp (_ \/ _) =>
    unwrap H; destruct H as [H | H]; wrap H
  end; canonicalize.
Ltac lImp H :=
  match type of H with Hyp (?P -> _) =>
    unwrap H; apply imply_to_or in H; (* ~ _ \/ _ *)
    destruct H as [H | H]; [ dropNeg H | wrap H ]
  end; canonicalize.
Ltac lIff H :=
  match type of H with Hyp (_ <-> _) =>
    unwrap H; destruct H as [H1 H2]; wrap H1; wrap H2
  end; canonicalize.
Ltac lBot H :=
  solve [match type of H with Hyp False =>
    unwrap H; destruct H
  end].
Ltac lTop H := (* equivalent to weakening *)
  match type of H with Hyp True =>
    unwrap H; destruct H
  end; canonicalize.
Ltac lNot H :=
  match type of H with Hyp (~ ?P) =>
    unwrap H; dropNeg H
  end; canonicalize.
Ltac lForall H t :=
  match type of H with Hyp (forall _, _) =>
    unwrap H; specialize (H t); wrap H
  end; canonicalize.
Ltac lExists H :=
  match type of H with Hyp (exists _, _) =>
    unwrap H; let x := fresh "x" in destruct H as [x H]; wrap H
  end; canonicalize.
Ltac lContract H := match type of H with Hyp ?T => myCut T; [|lExact H] end; canonicalize.
Ltac lWeaken H := clear H; canonicalize.

Ltac negExact H :=
  solve [unwrap H; repeat match goal with [ |- not (?P /\ ?Q) ] => apply or_not_and; try (solve [left; exact H]); right end].
Ltac negImp H :=
  match type of H with Hyp (~ (_ (* H1 *) -> _ (* H2 *))) =>
    unwrap H; apply imply_to_and in H;
    (* H : H1 /\ ~ H2 *)
    let H1 := fresh in let H2 := fresh in
    destruct H as [H1 H2];
    dropPos H1; wrap H2
  end.
Ltac negIff H :=
  match type of H with (Hyp (~ (_ <-> _))) =>
    unwrap H; apply not_and_or in H;
    destruct H as [H|H]; wrap H
  end.
Ltac negConj H :=
  match type of H with Hyp (~ (_ (* H1 *) /\ _ (* H2 *))) =>
    unwrap H; apply not_and_or in H;
    destruct H as [H|H]; wrap H
  end.
Ltac negDisj H :=
  match type of H with Hyp (~ (_ (* H1 *) \/ _ (* H2 *))) =>
    unwrap H; apply not_or_and in H;
    (* H : ~ H1 /\ ~ H2 *)
    let H1 := fresh in let H2 := fresh in
    destruct H as [ H1 H2 ];
    wrap H1; wrap H2
  end.
Ltac negNot H :=
  match type of H with Hyp (~ (~ _)) =>
    unwrap H; apply NNPP in H; dropPos H
  end.
Ltac negBot H :=
  match type of H with Hyp (~ False) =>
    unwrap H; clear H (* destruct does too much work *)
  end.
Ltac negTop H :=
  solve [match type of H with Hyp (~ True) =>
    unwrap H; contradict H; constructor
  end].
Ltac negForall H :=
  match type of H with Hyp (~ (forall _, _)) =>
    unwrap H; apply not_all_ex_not in H; let x := fresh "x" in destruct H as [x H]; wrap H
  end.
Ltac negExists H t :=
  match type of H with Hyp (~ (exists _, _)) =>
    unwrap H; apply not_ex_all_not with (n := t) in H; wrap H
  end.
Ltac negWeaken H := clear H.
Ltac negContract H :=
  let T := type of H in
  assert T by assumption.

Ltac rWrap tac H := posneg; tac H; negpos.
Ltac rExact H := posneg; negExact H.
Ltac rConj H := rWrap negConj H.
(* Alternatively, commit to a disjunction *)
Ltac rDisj H := rWrap negDisj H.
Ltac rImp H := rWrap negImp H.
Ltac rIff H := rWrap negIff H.
Ltac rTop H := posneg; negTop H.
Ltac rBot H := rWrap negBot H.
Ltac rNot H := rWrap negNot H.
Ltac rForall H := rWrap negForall H.
Ltac rExists H t := posneg; negExists H t; negpos.
Ltac rWeaken H := rWrap negWeaken H.
Ltac rContract H := rWrap negContract H.

Section universe.

Parameter U : Set.
Variable z : U. (* non-empty domain *)
Variable f : U -> U. (* FOL function *)
Variables A B C : Prop. (* some convenient things to instantiate with *)
Variables P Q R : U -> Prop.

Set Printing All.

Goal denote ( [True] |= [False] ).
  sequent.
    rBot Con0.
    lTop Hyp0.
Abort.

Goal denote ( [~~A] |= [A] ).
  sequent.
    lNot Hyp0.
    rNot Con0.
    lExact Hyp0.
Qed.

(* an example *)
Goal denote ( [ True; C /\ C; (~ True) \/ True ] |= [ False; False; False; ((A -> B) -> A) -> A ] ).
  sequent.
    lConj Hyp1.
    lContract Hyp3.
    lWeaken Hyp4.
    lDisj Hyp3.
    lNot Hyp3.
    rTop Con0.
    rImp Con3.
    lImp Hyp0.
    rImp Con0.
    lExact Hyp0.
    rContract Con0.
    rWeaken Con0.
    rExact Con2.
Qed.

Goal denote ( nil |= [ (forall x, P x) -> exists x, P x ] ).
  sequent.
    rImp Con0.
    lForall Hyp0 z.
    rExists Con0 z.
    lExact Hyp0.
Qed.

Goal denote ( nil |= [ (exists x, P x) -> ~ (forall x, ~ P x) ] ).
  sequent.
    rImp Con0.
    lExists Hyp0.
    rNot Con0.
    lForall Hyp0 x.
    lNot Hyp0.
    lExact Hyp0.
Qed.

Goal denote ( nil |= [ ((A -> B) -> A) -> A ] ).
  sequent.
    rImp Con0.
    lImp Hyp0.
    rImp Con0.
    lExact Hyp0.
    lExact Hyp0.
Qed.

Goal denote ( nil |= [ A \/ (A -> False) ] ).
  sequent.
    rDisj Con0.
    rImp Con1.
    lExact Hyp0.
Qed.

Goal denote ( nil |= [ exists x, ((exists y, P y) -> P x) ] ).
  sequent.
    rContract Con0.
    rExists Con0 z.
    rImp Con0.
    rWeaken Con0.
    lExists Hyp0.
    rExists Con0 x.
    rImp Con0.
    lExact Hyp1.
Qed.

(* slight rendering strangeness here *)
Goal denote ( nil |= [ A -> forall (x : U), A ] ).
  sequent.
    rImp Con0.
    rForall Con0.
    lExact Hyp0.
Qed.

Goal denote ( nil |= [ exists x, P x -> forall y, P y ] ).
  sequent.
    rContract Con0.
    rExists Con0 z.
    rImp Con0.
    rForall Con0.
    rWeaken Hyp0.
    rExists Con1 x.
    rImp Con1.
    lExact Hyp0.
Qed.

End universe.
