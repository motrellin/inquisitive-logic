From InqLog.FO Require Import Truth.
From InqLog.FO Require SingleUnaryPredicate.

(** * Double Negation Elimination *)

Definition DNE `{Signature} (phi : form) : form :=
  <{ (~ (~ phi)) -> phi }>.

Example DNE_classical `{Signature} :
  forall phi,
    classical (DNE phi) = classical phi.
Proof.
  intros phi.
  unfold DNE.
  rewrite classical_Impl.
  do 2 rewrite classical_Neg.
  apply andb_diag.
Qed.

(**
   By defining [PInterpretation] as a boolean predicate, we
   obtain double negation elimination of atoms.
 *)
Example support_valid_DNE_Pred `{Signature} :
  forall p args,
    support_valid <{DNE (Pred p args)}>.
Proof.
  intros p args M s1 a s2 H1 H2 w1 H3.
  rewrite support_Neg in H2.

  destruct (
    PInterpretation w1 p (fun arg : PAri p => referent (args arg) w1 a)
  ) eqn:H4; try reflexivity.

  exfalso.
  apply H2.
  exists (singleton w1).
  repeat split.
  -
    apply consistent_singleton_I.
  -
    intros w2 H5.
    apply contains_singleton_iff in H5.
    rewrite H5.
    exact H3.
  -
    rewrite support_Neg.
    intros [s3 [[w2 H5] [H6 H7]]].
    apply substate_singleton_E in H6 as [H6|H6].
    all: rewrite H6 in *; clear H6.
    +
      discriminate.
    +
      apply contains_singleton_iff in H5.
      rewrite support_Pred in H7.
      specialize (H7 _ (contains_singleton_refl w1)).
      congruence.
Qed.

(** * Validiy of [DNE]

   In this section, we want to point out that [DNE] is not
   schematically support-valid.

   For this, we will first try to prove this property to
   see, where the proof fails.

   After this, we will point out that [DNE] is at least
   valid for [classical] formulas.

   Last, we will present a counterexample with a
   non-classical formula.
 *)

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

Lemma truth_valid_DNE `{Model} :
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

Theorem support_valid_DNE_classical `{Signature} :
  forall phi,
    classical phi = true ->
    support_valid (DNE phi).
Proof.
  intros phi H1 M s a.
  apply classical_truth_conditional.
  {
    simpl.
    rewrite H1.
    reflexivity.
  }
  intros w H2.
  apply truth_valid_DNE.
Qed.

Module not_support_valid_DNE.

  Import SingleUnaryPredicate.
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
      specialize (H1 false eq_refl).
      discriminate.
    -
      simpl in H1.
      specialize (H1
        (singleton true)
        (substate_most_inconsistent_I _)
      ).
      assert (H2 :
        forall w, contains (singleton true) w -> w = true
      ).
      {
        intros w H2.
        apply contains_singleton_iff in H2.
        exact H2.
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
