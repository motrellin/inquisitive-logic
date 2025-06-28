From InqLog.FO Require Export Seq.
From InqLog.FO Require Import DNE.

Definition Kuroda `{Signature} (phi : form) : form :=
  <{(forall (~ ~ phi)) -> ~ ~ forall phi}>.

(** * Validity of [Kuroda] *)

Theorem support_valid_Kuroda `{Signature} :
  forall phi,
    support_valid (Kuroda phi).
Proof.
  intros phi.
  intros m s1 a.
  intros s2 H1 H2.
  apply truth_conditional_Neg.
  intros w H3.
  rewrite truth_Neg.
  intros H4.
  rewrite truth_Neg in H4.
  apply H4.
  rewrite truth_Forall.
  intros i.
  rewrite support_Forall in H2.
  specialize (H2 i).
  eapply truth_valid_DNE; try reflexivity.
  fold support.
  eapply persistency; try exact H2.
  intros w' H5.
  apply contains_singleton_iff in H5.
  rewrite H5.
  exact H3.
Qed.

Theorem Seq_Kuroda `{Signature} :
  forall ns phi,
    Seq nil ((pair ns (Kuroda phi)) :: nil).
Proof.
  intros ns1 phi.
  unfold Kuroda.
  eapply Seq_Impl_r.
  {
    apply InS_cons_I_hd; reflexivity.
  }
  intros ns2 H1.
  eapply Seq_Neg_r.
  {
    apply InS_cons_I_hd; reflexivity.
  }
  intros n1 H2.
  eapply Seq_Neg_l.
  {
    apply InS_cons_I_hd; reflexivity.
  }
  {
    reflexivity.
  }
  {
    apply InS_cons_I_hd; reflexivity.
  }
  eapply Seq_Forall_r.
  {
    apply InS_cons_I_hd; reflexivity.
  }
  eapply Seq_Forall_l with
    (t := Var 0).
  {
    apply InS_cons_I_tl.
    simpl.
    apply InS_cons_I_hd; reflexivity.
  }
  {
    exact I.
  }
  eapply Seq_Neg_l with
    (ns2 := n1 :: nil).
  {
    unfold Neg at 1.
    simpl.
    apply InS_cons_I_hd; reflexivity.
  }
  {
    apply cons_InS_sublist_I.
    -
      exact H2.
    -
      apply nil_InS_sublist_I.
  }
  {
    apply InS_cons_I_hd; reflexivity.
  }
  eapply Seq_Neg_r.
  {
    unfold Neg at 1.
    apply InS_cons_I_hd; reflexivity.
  }
  intros n H3.
  eapply Seq_persistency.
  {
    apply InS_cons_I_hd; reflexivity.
  }
  {
    simpl.
    apply InS_cons_I_tl.
    apply InS_cons_I_hd.
    f_equiv.
    rewrite hsubst_comp'.
    rewrite <- hsubst_id' with
      (phi := phi)
      at 2.
    apply hsubst_Proper; try reflexivity.
    intros [|x']; reflexivity.
  }
  apply InS_cons_E in H3 as [H3|H3].
  -
    rewrite H3.
    reflexivity.
  -
    apply InS_nil_E in H3.
    contradiction.
Qed.
