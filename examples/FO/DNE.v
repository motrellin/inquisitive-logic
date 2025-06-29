From InqLog.FO Require Import Truth.
From InqLog.FO Require SingleUnaryPredicate GenericModels.

(** * Double Negation Elimination *)

Definition DNE `{Signature} (phi : form) : form :=
  <{ (~ (~ phi)) -> phi }>.

Lemma truth_conditional_DNE `{Signature} :
  forall phi,
    truth_conditional phi ->
    truth_conditional (DNE phi).
Proof.
  intros phi H1.
  apply truth_conditional_Impl.
  exact H1.
Qed.

(** * Schematic Truth Validity of [DNE] *)

Theorem truth_valid_DNE `{Model} :
  forall phi w a,
    truth (DNE phi) w a.
Proof.
  intros phi w a.
  unfold DNE.
  rewrite truth_Impl.
  intros H1.
  do 2 rewrite truth_Neg in H1.
  apply NNPP.
  exact H1.
Qed.

(** * Atomic Validity of [DNE] *)

Lemma truth_conditional_support_valid_DNE_iff `{Signature} :
  forall phi,
    truth_conditional phi <->
    support_valid (DNE phi).
Proof.
  intros phi.
  split.
  -
    intros H1.
    intros M s a.
    apply truth_conditional_Impl; try exact H1.
    intros w H2.
    apply truth_valid_DNE.
  -
    intros H1.
    intros M s a H2.
    specialize (H1 M s a).
    unfold DNE in H1.
    rewrite support_Impl in H1.
    apply H1; try reflexivity.
    apply truth_conditional_Neg.
    intros w H3.
    do 2 rewrite truth_Neg.
    auto.
Qed.

Theorem support_valid_DNE_Pred `{Signature} :
  forall p args,
    support_valid <{DNE (Pred p args)}>.
Proof.
  intros p args.
  apply truth_conditional_support_valid_DNE_iff.
  apply truth_conditional_Pred.
Qed.

(** * Schematic Validiy of [DNE] *)

Theorem support_valid_DNE `{Signature} :
  forall phi,
    support_valid (DNE phi).
Proof.
  intros phi M s1 a s2 H1 H2.
  destruct (classic (consistent s2)) as [H3|H3].
  -
    apply NNPP.
    intros H4.
    rewrite support_Neg in H2.
    apply H2.
    exists s2.
    repeat split.
    +
      exact H3.
    +
      reflexivity.
    +
      rewrite support_Neg.
      intros [s3 [H5 [H6 H7]]].
      apply H4.
      eapply persistency.
      *
        exact H7.
      *
        Fail apply H6.
Abort.

Module not_support_valid_DNE.

  Import SingleUnaryPredicate.
  Import GenericModels.
  Existing Instance two_Worlds_Model.

  Lemma DNE_counterex_part_1 :
      most_inconsistent,pointed_assignment |=
        <{~ ~ ? Pred' (Var 0)}>.
  Proof.
    rewrite support_Neg.
    intros [s2 [[w H1] [H2 H3]]].
    rewrite support_Neg in H3.
    apply H3.
    exists (singleton w).
    repeat split.
    -
      apply consistent_singleton_I.
    -
      intros w' H4.
      apply contains_singleton_iff in H4.
      rewrite H4.
      exact H1.
    -
      apply truth_Iquest.
      exact I.
  Qed.

  Lemma DNE_counterex_part_2 :
    ~ (
        most_inconsistent,pointed_assignment |=
        <{? Pred' (Var 0)}>
    ).
  Proof.
    intros [H1|H1].
    -
      simpl in H1.
      now specialize (H1 false eq_refl).
    -
      simpl in H1.
      specialize (H1
        (singleton true)
        (substate_most_inconsistent_I _)
      ).
      assert (H2 :
        forall w, contains (singleton true) w -> if w then True else False
      ).
      {
        intros w H2.
        apply contains_singleton_iff in H2.
        now rewrite H2.
      }
      specialize (H1 H2 true).
      apply not_contains_singleton_iff in H1.
      apply H1.
      reflexivity.
  Qed.

  Theorem DNE_counterex :
    ~ (
        most_inconsistent,pointed_assignment |=
        DNE <{? Pred' (Var 0)}>
      ).
  Proof.
    intros H1.
    eapply DNE_counterex_part_2.
    apply H1; try reflexivity.
    apply DNE_counterex_part_1.
  Qed.

  Corollary not_support_valid_DNE :
    ~ forall phi,
        support_valid (DNE phi).
  Proof.
    intros H1.
    apply DNE_counterex.
    apply H1.
  Qed.

End not_support_valid_DNE.
