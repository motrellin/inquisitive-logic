From InqLog.FO Require Import Seq.

Definition CD `{Signature} (phi psi : form) : form :=
  <{
    (Forall <{(hsubst (ren (+1)) phi) \\/ psi}>) ->
    phi \\/(Forall psi)
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
      t,a |= phi
    )
  ) as [H3|H3].
  -
    left.
    exact H3.
  -
    right.
    intros i.
    rewrite support_Forall in H2.
    specialize (H2 i).
    destruct H2 as [H2|H2].
    +
      exfalso.
      apply H3.
      apply support_hsubst_var in H2.
      apply H2.
    +
      exact H2.
Qed.

Example Seq_ex_3 `{Signature} :
  forall ns phi psi,
    Seq
    ((pair ns <{(forall phi) \\/ psi}>) :: nil)
    ((pair ns (Forall (Idisj phi psi.|[ren (+1)]))) :: nil).
Proof with (
  try (left; simpl; reflexivity);
  try (right; left; simpl; reflexivity);
  try easy
).
  intros ns phi psi.
  eapply Seq_Forall_r...
  eapply Seq_Idisj_l...
  all: eapply Seq_Idisj_r...
  -
    eapply Seq_Forall_l with (t := Var 0)...
    eapply Seq_persistency.
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    {
      apply InS_cons_I_hd.
      f_equiv.
      rewrite <- hsubst_id' with
        (phi := phi)
        at 2.
      rewrite hsubst_comp'.
      apply hsubst_Proper; try reflexivity.
      intros [|]; reflexivity.
    }
    {
      reflexivity.
    }
  -
    eapply Seq_persistency...
Qed.
