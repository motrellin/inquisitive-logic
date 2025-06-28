From InqLog.FO Require Import Seq.

(** * Various Derivations using the Sequent Calculus *)

Example Seq_ex_1 `{Signature} :
  forall ns n p args,
    InS n ns ->
    Seq ((pair ns <{~ ~ Pred p args}>) :: nil)
    ((pair (n :: nil) <{Pred p args}>) :: nil).
Proof.
  intros ns1 n1 p args H1.
  apply Seq_Impl_l with
    (ns1 := ns1)
    (ns2 := n1 :: nil)
    (phi := <{~ Pred p args}>)
    (psi := Bot 0).
  -
    apply InS_cons_I_hd.
    reflexivity.
  -
    intros n2 H2.
    apply InS_cons_E in H2 as [H2|H2].
    +
      congruence.
    +
      contradict H2.
      apply InS_nil_E.
  -
    apply Seq_Impl_r with
      (ns := n1 :: nil)
      (phi := Pred p args)
      (psi := Bot 0).
    +
      apply InS_cons_I_hd.
      reflexivity.
    +
      intros ns2 H2.
      apply InS_sublist_singleton_E in H2 as [H2|H2].
      *
        apply Seq_id with
          (ns1 := ns2)
          (ns2 := n1 :: nil)
          (p := p)
          (args := args).
        --
           apply InS_cons_I_hd.
           reflexivity.
        --
           do 2 apply InS_cons_I_tl.
           apply InS_cons_I_hd.
           reflexivity.
        --
           exact H2.
      *
        apply InS_eq_nil in H2.
        subst ns2.
        apply Seq_empty with
          (phi := Bot 0).
        apply InS_cons_I_hd.
        reflexivity.
  -
    apply Seq_Bot_l with
      (n := n1)
      (ns := n1 :: nil)
      (x := 0).
    +
      apply InS_cons_I_hd.
      reflexivity.
    +
      apply InS_cons_I_hd.
      reflexivity.
Qed.

Print Assumptions Seq_ex_1.

Example Seq_ex_2 `{Signature} :
  forall ns phi psi,
    Seq
    ((pair ns <{iexists phi}>) :: nil)
    ((pair ns <{iexists ~ psi -> phi}>) :: nil).
Proof with (
  try (right; left; simpl; reflexivity);
  try (left; simpl; reflexivity);
  try easy
).
  intros ns1 phi psi.
  eapply Seq_Iexists_l...
  eapply Seq_Iexists_r with (t := Var 0)...
  eapply Seq_Impl_r...
  intros ns' H1.
  simpl.
  eapply Seq_persistency.
  {
    apply InS_cons_I_tl.
    apply InS_cons_I_hd.
    reflexivity.
  }
  {
    apply InS_cons_I_hd.
    f_equiv.
    rewrite hsubst_comp'.
    rewrite <- hsubst_id' at 1.
    apply hsubst_Proper; try reflexivity.
    intros [|]; reflexivity.
  }
  exact H1.
Qed.

Print Assumptions Seq_ex_2.
