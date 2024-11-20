From InqLog.FO Require Export Syntax States.

(** * (Variable) Assignments *)

(** * Support satisfaction *)

Definition assignment `{Model} : Type := var -> Individual.

Fixpoint referent `{Model} (t : term) : World -> assignment -> Individual :=
  match t with
  | Var v =>
      fun _ g =>
      g v
  | Func f args =>
      fun w g =>
      FInterpretation w f (fun arg => referent (args arg) w g)
  end.

Fixpoint support `{Model} (phi : form) : state -> assignment -> Prop :=
  match phi with
  | Pred p args =>
      fun s a =>
      forall (w : World),
        s w = true ->
        PInterpretation w p (fun arg => referent (args arg) w a) = true

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

(** ** Basic properties *)

Proposition persistency `{Model} :
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

Proposition empty_state_property `{Model} :
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

(** ** Ruling out a formula *)

Definition ruling_out `{Model} (s : state) (phi : form) (a : assignment) :=
  ~ exists t,
    consistent t /\
    substate t s /\
    support phi t a.

(** ** Support conditions for defined connectives *)

Proposition support_Neg `{Model} :
  forall phi s a,
    support <{~ phi}> s a <->
    ruling_out s phi a.
Proof.
  simpl.
  intros phi s a.
  split.
  -
    intros H1 [t [[w H2] [H3 H4]]].
    enough (t w = false). congruence.
    apply H1.
    exact H3.
    exact H4.
  -
    intros H1 t H2 H3 w.
    destruct (t w) eqn:H5.
    +
      exfalso.
      eapply H1.
      exists t.
      repeat split.
      *
        exists w.
        exact H5.
      *
        exact H2.
      *
        exact H3.
    +
      reflexivity.
Qed.

Proposition support_Top `{Model} :
  forall s a,
    support <{Top}> s a.
Proof.
  intros s a.
  unfold Top.
  rewrite support_Neg.
  intros [t [[w H1] [H2 H3]]].
  specialize (H3 w).
  congruence.
Qed.

Proposition support_Disj `{Model} :
  forall phi1 phi2 s a,
  support <{phi1 \/ phi2}> s a <->
  ~ exists t,
    consistent t /\
    substate t s /\
    ruling_out t phi1 a /\
    ruling_out t phi2 a.
Proof.
  intros phi1 phi2 s a.
  unfold Disj.
  split.
  -
    intros H1.
    rewrite support_Neg in H1.
    intros [t [H2 [H3 [H4 H5]]]].
    apply H1.
    exists t.
    repeat split; try rewrite support_Neg; assumption.
  -
    intros H1.
    rewrite support_Neg.
    intros [t [H2 [H3 [H4 H5]]]].
    apply H1.
    exists t.
    repeat split; try rewrite <- support_Neg; assumption.
Qed.

Proposition support_Iff `{Model} :
  forall phi1 phi2 s a,
    support <{phi1 <-> phi2}> s a <->
    forall t,
      substate t s ->
      support phi1 t a <->
      support phi2 t a.
Proof.
  firstorder.
Qed.

(** * Support consequence *)

Definition support_conseq `{S : Signature} : relation form :=
  fun phi psi =>
  forall `(M : @Model S) s a,
    support phi s a ->
    support psi s a.

Instance support_conseq_Preorder `{Signature} :
  PreOrder support_conseq.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Impl `{Signature} :
  forall phi1 phi2 psi1 psi2,
    support_conseq phi1 phi2 ->
    support_conseq psi1 psi2 ->
    support_conseq <{phi2 -> psi1}> <{phi1 -> psi2}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Conj `{Signature} :
  forall phi1 phi2 psi1 psi2,
    support_conseq phi1 phi2 ->
    support_conseq psi1 psi2 ->
    support_conseq <{phi1 /\ psi1}> <{phi2 /\ psi2}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Idisj `{Signature} :
  forall phi1 phi2 psi1 psi2,
    support_conseq phi1 phi2 ->
    support_conseq psi1 psi2 ->
    support_conseq <{phi1 \\/ psi1}> <{phi2 \\/ psi2}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Forall `{Signature} :
  forall phi1 phi2,
    support_conseq phi1 phi2 ->
    support_conseq <{forall phi1}> <{forall phi2}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Iexists `{Signature} :
  forall phi1 phi2,
    support_conseq phi1 phi2 ->
    support_conseq <{iexists phi1}> <{iexists phi2}>.
Proof.
  intros * H1 M s a H2.
  simpl support in *.
  destruct H2 as [i H2].
  exists i.
  auto.
Qed.

(** * Support valid formulas *)

Definition support_valid `{S : Signature} (phi : form) : Prop :=
  forall `(M : @Model S) s a,
    support phi s a.

Remark support_valid_conseq_valid `{Signature} :
  forall phi psi,
    support_valid phi ->
    support_conseq phi psi ->
    support_valid psi.
Proof.
  firstorder.
Qed.

Remark support_valid_Impl_conseq `{S : Signature} :
  forall phi psi,
    support_valid <{phi -> psi}> ->
    support_conseq phi psi.
Proof.
  intros phi psi H1 M s a H2.
  eapply H1.
  -
    reflexivity.
  -
    exact H2.
Qed.

Lemma support_valid_DNE_Pred `{Signature} :
  forall p args,
    support_valid <{DNE (Pred p args)}>.
Proof.
  intros p args M s1 a s2 H1 H2 w1 H3.

  destruct (
    PInterpretation w1 p (fun arg : PAri p => referent (args arg) w1 a)
  ) eqn:H4.
  -
    reflexivity.
  -
    rewrite support_Neg in H2.
    exfalso.
    apply H2.
    exists (singleton w1).
    repeat split.
    +
      exists w1.
      apply singleton_true.
      reflexivity.
    +
      intros w2 H5.
      apply singleton_true in H5.
      congruence.
    +
      rewrite support_Neg.
      intros [s3 [[w2 H5] [H6 H7]]].
      apply substate_singleton in H6 as [H6|H6].
      all: rewrite H6 in *; clear H6.
      *
        discriminate.
      *
        apply singleton_true in H5.
        subst w2.
        simpl in H7.
        rewrite H7 in H4.
        discriminate.
        apply singleton_true.
        reflexivity.
Qed.
