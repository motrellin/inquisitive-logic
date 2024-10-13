From Autosubst Require Export Autosubst.
From Coq Require Import Bool Nat Relations RelationClasses Morphisms Setoid FunctionalExtensionality.

(* Signatures *)

Class Signature :=
  {
    PSymb : Type;
    PAri : PSymb -> Type;
    FSymb : Type;
    FAri : FSymb -> Type;
    rigid : FSymb -> bool
  }.

(* Definition of terms *)

Inductive term `{Signature} :=
  | Var : var -> term
  | Func : forall (f : FSymb), (FAri f -> term) -> term.

(* Autosubst-stuff about terms *)

Instance Ids_term `{Signature} : Ids term.
Proof. derive. Defined.

Instance Rename_term `{Signature} : Rename term.
Proof. derive. Defined.

Instance Subst_term `{Signature} : Subst term.
Proof. derive. Defined.

Instance SubstLemmas_term `{Signature} : SubstLemmas term.
Proof. derive. Qed.

(* syntax of first-order formulas including inquisitive operators *)

Inductive form `{Signature} :=
  (* predicate symbols *)
  | Pred : forall (p : PSymb), (PAri p -> term) -> form

  (* propositional connectives *)
  | Bot (v : var) : form
  | Impl : form -> form -> form
  | Conj : form -> form -> form
  | Idisj : form -> form -> form

  (* first-order connectives *)
  | Forall : {bind term in form} -> form
  | Iexists : {bind term in form} -> form.

(* Autosubst-stuff about formulas *)

Instance HSubst_form `{Signature} : HSubst term form.
Proof. derive. Defined.

Instance Ids_form `{Signature} : Ids form.
Proof. derive. Defined.

Instance Rename_form `{Signature} : Rename form.
Proof. derive. Defined.

Instance Subst_form `{Signature} : Subst form.
Proof. derive. Defined.

Instance HSubstLemmas_form `{Signature} : HSubstLemmas term form.
Proof. derive. Qed.

Instance SubstHSubstComp_term_form `{Signature} : SubstHSubstComp term form.
Proof. derive. Qed.

Instance SubstLemmas_form `{Signature} : SubstLemmas form.
Proof. derive. Qed.

(* Other defined connectives *)

Section defined_connectives.

  Context `{Signature}.

  Definition Neg (f : form) := Impl f (Bot 0).
  Definition Top := Neg (Bot 0).
  Definition Disj (f1 f2 : form) := Neg (Conj (Neg f1) (Neg f2)).
  Definition Iff (f1 f2 : form) := Conj (Impl f1 f2) (Impl f2 f1).
  Definition Exists (f : form) := Forall (Neg f).
  Definition Iquest (f : form) := Idisj f (Neg f).

End defined_connectives.

(* Models *)

Class Model `{Signature} :=
  {
    World : Type;
    Individual : Type;
    Individual_inh : Individual;

    PInterpretation :
      forall (w : World) (p : PSymb),
        (PAri p -> Individual) ->
        Prop;

    FInterpretation :
      forall (w : World) (f : FSymb),
        (FAri f -> Individual) ->
        Individual;

    rigidity :
      forall (f : FSymb),
        rigid f = true ->
        forall (w w' : World),
          FInterpretation w f = FInterpretation w' f
  }.

(* (Variable) Assignments *)

Definition assignment `{Model} : Type := var -> Individual.

Fixpoint referent `{Model} (t : term) : World -> assignment -> Individual :=
  match t with
  | Var v =>
      fun _ g =>
      g v
  | Func f ari =>
      fun w g =>
      let args :=
        fun arg =>
        referent (ari arg) w g
      in
      FInterpretation w f args
  end.

Definition state `{Model} : Type := World -> bool.

Definition state_eq `{Model} : relation state :=
  fun s t =>
  forall w,
    s w = t w.

Instance state_eq_Equiv `{Model} : Equivalence state_eq.
Proof.
  split.
  -
    intros s w.
    reflexivity.
  -
    intros s t H1 w.
    rewrite H1.
    reflexivity.
  -
    intros s t u H1 H2 w.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Definition empty_state `{Model} : state := fun _ => false.

Definition substate `{Model} (t s : state) : Prop :=
  forall w,
    t w = true -> s w = true.

Instance substate_Proper `{Model} : Proper (state_eq ==> state_eq ==> iff) substate.
Proof.
  intros s1 s2 H1 t1 t2 H2.
  unfold substate.
  unfold state_eq in *.
  firstorder.
  -
    rewrite <- H2.
    apply H3.
    rewrite H1.
    exact H4.
  -
    rewrite H2.
    apply H3.
    rewrite <- H1.
    exact H4.
Qed.

Fixpoint support `{Model} (phi : form) : state -> assignment -> Prop :=
  match phi with
  | Pred p ari =>
      fun s a =>
      forall (w : World),
        s w = true ->
        let args :=
          fun arg =>
          referent (ari arg) w a
        in
        PInterpretation w p args

  | Bot _ =>
      fun s a =>
      forall (w : World),
        s w = false

  | Impl phi1 phi2 =>
      fun s a =>
      forall (t : state),
        substate t s ->
        support phi1 t a ->
        support phi2 t a

  | Conj phi1 phi2 =>
      fun s a =>
      support phi1 s a /\
      support phi2 s a

  | Idisj phi1 phi2 =>
      fun s a =>
      support phi1 s a \/
      support phi2 s a

  | Forall phi1 =>
      fun s a =>
      forall (i : Individual),
        support phi1 s (i .: a)

  | Iexists phi1 =>
      fun s a =>
      exists (i : Individual),
        support phi1 s (i .: a)

  end.

Instance support_Proper `{Model} :
  forall phi,
    Proper (state_eq ==> eq ==> iff) (support phi).
Proof.
  all: intros phi s1 s2 H1 a1 a2 H2.
  unfold state_eq in H1.
  subst a2.
  generalize dependent a1.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros a1.
  all: simpl in *.
  -
    split.
    all: intros H3 w H4.
    +
      apply H3.
      rewrite H1.
      exact H4.
    +
      apply H3.
      rewrite <- H1.
      exact H4.
  -
    firstorder; congruence.
  -
    unfold substate.
    split.
    all: intros H3 s3 H4 H5.
    +
      apply H3.
      *
        intro.
        rewrite H1.
        auto.
      *
        exact H5.
    +
      apply H3.
      *
        intro.
        rewrite <- H1.
        auto.
      *
        exact H5.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
Qed.

Theorem persistency `{Model} :
  forall s t a phi,
    support phi s a ->
    substate t s ->
    support phi t a.
Proof.
  intros s t a phi.
  revert s t a.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].

  all: intros s t a H1 H2.
  all: simpl in *.
  -
    firstorder.
  -
    intros w.
    unfold substate in H2.
    specialize (H1 w).
    specialize (H2 w).
    destruct (t w).
    +
      rewrite H2 in H1.
      discriminate.
      reflexivity.
    +
      reflexivity.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    destruct H1 as [i H1].
    eapply IH1 in H1 as H3.
    eexists.
    exact H3.
    exact H2.
Qed.

Theorem empty_state_property `{Model} :
  forall (a : assignment) (phi : form),
    support phi empty_state a.
Proof.
  intros a phi.
  revert a.

  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros a.
  all: unfold empty_state in *.
  all: simpl in *.
  -
    discriminate.
  -
    reflexivity.
  -
    intros t H1 H2.
    unfold substate in H1.
    enough (forall w, t w = false).
    admit. (* TODO Define state equivalence *)
    admit. (* TODO Should be easy to derive, just have a look on the prop-chapter *)
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
    exact Individual_inh.
Admitted.
