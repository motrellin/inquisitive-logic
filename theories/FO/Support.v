From InqLog.FO Require Export Syntax States.

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
  all: simpl in *.
  -
    discriminate.
  -
    reflexivity.
  -
    intros t H1 H2.
    unfold substate in H1.
    enough (state_eq t empty_state).
    specialize (IH2 a).
    rewrite <- H3 in IH2.
    exact IH2.

    intros w.
    specialize (H1 w).
    destruct (t w).
    +
      unfold empty_state in H1.
      specialize (H1 eq_refl).
      discriminate.
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
    exact Individual_inh.
Qed.
