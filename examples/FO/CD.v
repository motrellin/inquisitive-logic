From InqLog.FO Require Import Seq.

Definition CD `{Signature} (phi psi : form) : form :=
  <{
    (Forall <{phi \\/ (hsubst (ren (+1)) psi)}>) ->
    (Forall phi) \\/ psi
  }>.

Theorem support_valid_CD `{Signature} :
  forall phi psi,
    support_valid (CD phi psi).
Proof.
  intros phi psi.
  intros M s a.
  intros t H1 H2.
  destruct (
    classic (
      t,a |= psi
    )
  ) as [H3|H3].
  -
    right.
    exact H3.
  -
    left.
    intros i.
    rewrite support_Forall in H2.
    specialize (H2 i).
    destruct H2 as [H2|H2].
    +
      exact H2.
    +
      exfalso.
      apply H3.
      apply support_hsubst_var in H2.
      apply H2.
Qed.

Theorem Seq_CD `{Signature} :
  forall ns phi psi,
    Seq nil ((pair ns (CD phi psi)) :: nil).
Proof with (
  try (left; simpl; reflexivity);
  try (right; left; simpl; reflexivity);
  try easy
).
  intros ns phi psi.
  unfold CD.
  eapply Seq_Impl_r...
  intros ns' H1.
  eapply Seq_Idisj_r...
  eapply Seq_Forall_r...
  eapply Seq_Forall_l with (t := Var 0)...
  eapply Seq_Idisj_l...
  -
    eapply Seq_persistency...
    apply InS_cons_I_hd.
    rewrite hsubst_comp'.
    f_equiv.
    rewrite <- hsubst_id' with (phi := phi) at 2.
    apply hsubst_Proper; try reflexivity.
    intros [|x']; reflexivity.
  -
    eapply Seq_persistency...
    do 2 apply InS_cons_I_tl.
    apply InS_cons_I_hd.
    repeat rewrite hsubst_comp'.
    f_equiv.
Qed.
