From InqLog.FO Require Export Support.

From Coq Require Import Bool.

(** * Truth satisfaction *)

Definition truth `{Model} (phi : form) (w : World) (a : assignment) : Prop :=
  support phi (singleton w) a.

(** * Truth decidable models *)

(* TODO: Investigate, if/how these axioms can be simplified: *)
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

(** * Truth satisfaction rules *)
(** ** Truth satisfaction rules for basic connectives *)

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

(** ** Truth satisfaction for defined connectives *)

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

(** * Truth-conditional formulas *)

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

Definition truth_conditional `{S : Signature} (phi : form) : Prop :=
  forall `(M : @Model S) (s : state) (a : assignment),
    support phi s a <->
    forall w,
      s w = true ->
      truth phi w a.

Proposition classic_truth_conditional `{S : Signature} :
  forall phi,
    classic phi = true ->
    truth_conditional phi.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: simpl in *.
  -
    intros _ M s a.
    split.
    +
      intros H1 w1 H2.
      rewrite truth_Pred.
      auto.
    +
      intros H1 w1 H2.
      rewrite <- truth_Pred.
      auto.
  -
    intros _ M s a.
    split.
    +
      congruence.
    +
      intros H1 w1.
      specialize (H1 w1).
      destruct (s w1).
      *
        rewrite truth_Bot in H1.
        easy.
      *
        reflexivity.
  -
    intros H1 M s a.
    apply andb_true_iff in H1 as [H1 H2].
    specialize (IH1 H1).
    specialize (IH2 H2).
    split.
    +
      intros H3 w1 H4.
      rewrite truth_Impl.
      intros H5.
      apply IH2.
      intros w2 H6.
      apply singleton_true in H6.
      subst w2.
      simpl in H3.
      apply H3.
      *
        intros w2 H7.
        apply singleton_true in H7.
        subst w2.
        exact H4.
      *
        exact H5.
    +
      intros H3 t H4 H5.
      apply IH2.
      intros w1 H6.
      specialize (H3 w1).
      rewrite truth_Impl in H3.
      apply H3.
      *
        apply H4.
        exact H6.
      *
        eapply IH1 in H5.
        --
           exact H5.
        --
           exact H6.
  -
    intros H1 M s a.
    apply andb_true_iff in H1 as [H1 H2].
    specialize (IH1 H1 M s a).
    specialize (IH2 H2 M s a).
    firstorder using truth_Conj.
  -
    discriminate.
  -
    intros H1 M s a.
    specialize (IH1 H1 M s).
    split.
    +
      intros H2 w1 H3.
      rewrite truth_Forall.
      intros i1.
      apply IH1.
      *
        exact (H2 i1).
      *
        exact H3.
    +
      intros H2 i1.
      apply IH1.
      intros w1 H3.
      apply H2.
      exact H3.
  -
    discriminate.
Qed.
