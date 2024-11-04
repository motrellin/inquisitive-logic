From InqLog.FO Require Export Support.

Definition truth `{Model} (phi : form) (w : World) (a : assignment) : Prop :=
  support phi (singleton w) a.

Class TDModel `{Model} :=
  {
    current_ax_1 :
      forall `{Model} phi w a,
        {forall i, truth phi w (i .: a)} +
        {exists i, ~ truth phi w (i .: a)};
    current_ax_2 :
      forall `{Model} phi w a,
        {forall i, ~ truth phi w (i .: a)} +
        {exists i, truth phi w (i .: a)}
  }.

Lemma truth_decidable `{M : TDModel} :
  forall phi w a,
    {truth phi w a} + {~ truth phi w a}.
Proof.
  intros *.
  revert w a.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros w a.
  -
    simpl.
    destruct (PInterpretation w p (fun arg => referent (args arg) w a)) eqn:H1.
    +
      left.
      intros w' H2.
      apply singleton_true in H2.
      subst w'.
      exact H1.
    +
      right.
      intros H2.
      rewrite H2 in H1.
      *
        discriminate.
      *
        apply singleton_true.
        reflexivity.
  -
    right.
    intros H1.
    specialize (H1 w).
    apply singleton_false in H1.
    apply H1.
    reflexivity.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    destruct IH1 as [IH1|IH1].
    +
      destruct IH2 as [IH2|IH2].
      *
        left.
        intros t H1 H2.
        apply substate_singleton in H1 as [H1|H1].
        all: rewrite H1.
        all: auto using empty_state_property.
      *
        right.
        intros H1.
        simpl in H1.
        apply IH2.
        apply H1.
        --
           reflexivity.
        --
           exact IH1.
    +
      left.
      intros t H1 H2.
      apply substate_singleton in H1 as [H1|H1].
      *
        rewrite H1.
        apply empty_state_property.
      *
        rewrite H1 in H2.
        contradiction.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    firstorder.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    firstorder.
  -
    simpl.
    specialize (IH1 w).
    assert (H1 :
      forall i,
        {support phi1 (singleton w) (i .: a)} +
        {~ support phi1 (singleton w) (i .: a)}
    ). firstorder. clear IH1.

    destruct (current_ax_1 phi1 w a).
    all: firstorder.
  -
    specialize (IH1 w).
    assert (H1 :
      forall i,
        {support phi1 (singleton w) (i .: a)} +
        {~ support phi1 (singleton w) (i .: a)}
    ). firstorder. clear IH1.

    destruct (current_ax_2 phi1 w a) as [H2|H2].
    all: firstorder.
Qed.

Proposition truth_Pred `{Model} :
  forall p args w a,
    truth (Pred p args) w a <->
    PInterpretation w p (fun arg => referent (args arg) w a) = true.
Proof.
  intros p ari w a.
  unfold truth.
  simpl.
  split.
  -
    intros H1.
    apply H1.
    apply singleton_true.
    reflexivity.
  -
    intros H1 w' H2.
    enough (w' = w).
    subst w'.
    exact H1.
    apply singleton_true.
    exact H2.
Qed.

Proposition truth_Bot `{Model} :
  forall v w a,
    (truth (Bot v) w a) <-> False.
Proof.
  intros ? w a.
  firstorder.
  unfold truth in H1.
  simpl in H1.
  specialize (H1 w).
  apply singleton_false in H1.
  congruence.
Qed.

Proposition truth_Conj `{Model} :
  forall phi1 phi2 w a,
    truth (Conj phi1 phi2) w a <->
    (
      truth phi1 w a /\
      truth phi2 w a
    ).
Proof.
  firstorder.
Qed.

Proposition truth_Idisj `{Model} :
  forall phi1 phi2 w a,
    truth (Idisj phi1 phi2) w a <->
    truth phi1 w a \/
    truth phi2 w a.
Proof.
  firstorder.
Qed.

Proposition truth_Impl `{Model} :
  forall phi1 phi2 w a,
  truth (Impl phi1 phi2) w a <->
  (
    truth phi1 w a ->
    truth phi2 w a
  ).
Proof.
  intros phi1 phi2 w a.
  unfold truth.
  simpl in *.
  split.
  -
    firstorder.
  -
    intros H1 t H2 H3.
    enough (state_eq t empty_state \/ state_eq t (singleton w)) as [H4|H4].
    +
      rewrite H4.
      apply empty_state_property.
    +
      rewrite H4 in *.
      auto.
    +
      apply substate_singleton.
      exact H2.
Qed.

Proposition truth_Forall `{Model} :
  forall phi w a,
    truth (Forall phi) w a <->
    forall i,
      truth phi w (i .: a).
Proof.
  firstorder.
Qed.

Proposition truth_Iexists `{Model} :
  forall phi w a,
    truth (Iexists phi) w a <->
    exists i,
      truth phi w (i .: a).
Proof.
  firstorder.
Qed.

(* Defined Connectives *)

Proposition truth_Neg `{Model} :
  forall phi w a,
    truth (Neg phi) w a <->
    ~ truth phi w a.
Proof.
  intros phi w a.
  unfold Neg.
  rewrite truth_Impl.
  rewrite truth_Bot.
  reflexivity.
Qed.

Proposition truth_Disj `{M : TDModel} :
  forall phi1 phi2 w a,
    truth (Disj phi1 phi2) w a <->
    truth phi1 w a \/
    truth phi2 w a.
Proof.
  intros phi1 phi2 w a.
  unfold Disj.
  rewrite truth_Neg.
  rewrite truth_Conj.
  do 2 rewrite truth_Neg.
  pose proof (truth_decidable phi1 w a) as H1.
  pose proof (truth_decidable phi2 w a) as H2.
  firstorder.
Qed.

Proposition truth_Exists `{M : TDModel} :
  forall phi w a,
    truth (Exists phi) w a <->
    exists i,
      truth phi w (i .: a).
Proof.
  intros phi w a.
  unfold Exists.
  rewrite truth_Neg.
  rewrite truth_Forall.
  split.
  -
    intros H1.
    assert (H1' : ~ forall i, ~ truth phi w (i .: a)).
    {
      intros H2.
      apply H1.
      intros i.
      rewrite truth_Neg.
      easy.
    }
    clear H1.
    rename H1' into H1.

    destruct (current_ax_2 phi w a) as [H2|H2].
    all: firstorder.
  -
    intros [i H1] H2.
    specialize (H2 i).
    rewrite truth_Neg in H2.
    contradiction.
Qed.

Definition truth_conditional `{Signature} (phi : form) : Prop :=
  forall (M : Model) (s : state) (a : assignment),
    support phi s a <->
    forall w,
      s w = true ->
      truth phi w a.

Fixpoint classical_variant `{Signature} (phi : form) : form :=
  match phi with
  | Pred p ari =>
      Pred p ari

  | Bot v =>
      Bot v

  | Impl phi1 phi2 =>
      Impl (classical_variant phi1) (classical_variant phi2)

  | Conj phi1 phi2 =>
      Conj (classical_variant phi1) (classical_variant phi2)

  | Idisj phi1 phi2 =>
      Disj (classical_variant phi1) (classical_variant phi2)

  | Forall phi1 =>
      Forall (classical_variant phi1)

  | Iexists phi1 =>
      Exists (classical_variant phi1)

  end.

Proposition truth_classical_variant `{M : TDModel} :
  forall phi w a,
    truth phi w a <->
    truth (classical_variant phi) w a.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros w a.
  all: simpl.
  all: try reflexivity.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    do 2 rewrite truth_Impl.
    firstorder.
  -
    firstorder.
  -
    rewrite truth_Idisj.
    rewrite truth_Disj.
    firstorder.
  -
    firstorder.
  -
    rewrite truth_Iexists.
    rewrite truth_Exists.
    firstorder.
Qed.

(* TODO: Investigate, if/how these axioms can be simplified: *)
Print Assumptions truth_classical_variant.
