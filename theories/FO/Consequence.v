From InqLog.FO Require Export Truth.

Definition support_conseq
  `{S : Signature}
  (Phi : list form)
  (psi : form) :

  Prop :=

  forall `(M : @Model S) s a,
    support_mult s a Phi ->
    (s, a |= psi).

Remark support_valid_charac_support_conseq `{Signature} :
  forall phi,
    support_conseq nil phi <->
    support_valid phi.
Proof.
  intros phi.
  split.
  -
    intros H1 M s a.
    apply H1.
    apply mult_nil_I.
  -
    intros H1 M s a H2.
    apply H1.
Qed.

Lemma support_conseq_in `{Signature} :
  forall cxt phi,
    InS phi cxt ->
    support_conseq cxt phi.
Proof.
  intros cxt phi H1 M s a H2.
  apply H2.
  exact H1.
Qed.

Lemma support_conseq_refl `{S : Signature} :
  forall phi,
    support_conseq (phi :: nil) phi.
Proof.
  intros phi.
  apply support_conseq_in.
  left.
  reflexivity.
Qed.

Lemma support_conseq_trans `{Signature} :
  forall cxt1 cxt2 phi,
    (forall psi, InS psi cxt2 -> support_conseq cxt1 psi) ->
    support_conseq cxt2 phi ->
    support_conseq cxt1 phi.
Proof.
  intros cxt1 cxt2 phi H1 H2 M s a H3.
  apply H2.
  intros psi H4.
  apply H1.
  -
    exact H4.
  -
    exact H3.
Qed.

Lemma support_conseq_weakening_nil `{Signature} :
  forall cxt phi,
    support_conseq nil phi ->
    support_conseq cxt phi.
Proof.
  intros cxt phi H1 M s a H2.
  apply H1.
  apply mult_nil_I.
Qed.

Lemma support_conseq_weakening_cons_hd `{Signature} :
  forall cxt phi,
    support_conseq (phi :: cxt) phi.
Proof.
  intros cxt phi.
  apply support_conseq_in.
  left.
  reflexivity.
Qed.

Lemma support_conseq_weakening_cons_tl `{Signature} :
  forall cxt phi psi,
    support_conseq cxt psi ->
    support_conseq (phi :: cxt) psi.
Proof.
  intros cxt phi psi H1 M s a H3.
  apply H1.
  apply mult_cons_E_tl in H3.
  exact H3.
Qed.

Lemma support_conseq_weakening_1 `{S : Signature} :
  forall cxt1 cxt2 phi,
    support_conseq cxt1 phi ->
    support_conseq (cxt1 ++ cxt2) phi.
Proof.
  intros cxt1 cxt2 phi H1 M s a H2.
  apply H1.
  eapply mult_app_E_1.
  exact H2.
Qed.

Lemma support_conseq_weakening_2 `{S : Signature} :
  forall cxt1 cxt2 phi,
    support_conseq cxt2 phi ->
    support_conseq (cxt1 ++ cxt2) phi.
Proof.
  intros cxt1 cxt2 phi H1 M s a H2.
  apply H1.
  eapply mult_app_E_2.
  exact H2.
Qed.

Lemma support_conseq_Bot_I `{Signature} :
  forall cxt phi,
    support_conseq cxt phi ->
    support_conseq cxt <{~ phi}> ->
    support_conseq cxt (Bot 0).
Proof.
  intros cxt phi H1 H2 M s a H3 w H4.
  specialize (H1 _ _ _ H3).
  specialize (H2 _ _ _ H3).
  rewrite support_Neg in H2.
  apply H2.
  exists s.
  repeat split.
  -
    exists w.
    exact H4.
  -
    reflexivity.
  -
    exact H1.
Qed.

Lemma support_conseq_Bot_E `{S : Signature} :
  forall cxt phi,
    support_conseq cxt (Bot 0) ->
    support_conseq cxt phi.
Proof.
  intros cxt phi H1 M s a H2.
  specialize (H1 M s a H2).
  enough (H3 : state_eq s empty_state).
  {
    rewrite H3.
    apply empty_state_property.
  }
  rewrite support_Bot in H1.
  apply state_eq_empty_state_iff_not_consistent.
  intros [w H3].
  specialize (H1 w).
  contradiction.
Qed.

Lemma support_conseq_Impl_I `{S : Signature} :
  forall cxt phi psi,
    support_conseq (phi :: cxt) psi ->
    support_conseq cxt <{phi -> psi}>.
Proof.
  intros cxt phi psi H1 M s a H2.
  intros t H3 H4.
  apply H1.
  apply mult_cons_I.
  -
    exact H4.
  -
    eapply persistency_support_mult.
    all: eassumption.
Qed.

Lemma support_conseq_Impl_E `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt phi ->
    support_conseq cxt <{phi -> psi}> ->
    support_conseq cxt psi.
Proof.
  intros cxt phi psi H1 H2 M s a H3.
  specialize (H1 _ _ _ H3).
  specialize (H2 _ _ _ H3).
  rewrite support_Impl in H2.
  apply H2.
  -
    reflexivity.
  -
    apply H1.
Qed.

Lemma support_conseq_Conj_I `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt phi ->
    support_conseq cxt psi ->
    support_conseq cxt <{phi /\ psi}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Conj_E1 `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt <{phi /\ psi}> ->
    support_conseq cxt phi.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Conj_E2 `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt <{phi /\ psi}> ->
    support_conseq cxt psi.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Idisj_I1 `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt phi ->
    support_conseq cxt <{phi \\/ psi}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Idisj_I2 `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt psi ->
    support_conseq cxt <{phi \\/ psi}>.
Proof.
  firstorder.
Qed.

Lemma support_conseq_Idisj_E `{S : Signature} :
  forall cxt phi psi chi,
    support_conseq cxt <{phi \\/ psi}> ->
    support_conseq (phi :: cxt) chi ->
    support_conseq (psi :: cxt) chi ->
    support_conseq cxt chi.
Proof.
  intros cxt phi psi chi H1 H2 H3 M s a H4.
  specialize (H1 _ _ _ H4).
  rewrite support_Idisj in H1.
  destruct H1 as [H1|H1].
  -
    apply H2.
    apply mult_cons_I.
    +
      exact H1.
    +
      exact H4.
  -
    apply H3.
    apply mult_cons_I.
    +
      exact H1.
    +
      exact H4.
Qed.

Lemma support_conseq_Forall_I `{S : Signature} :
  forall cxt phi,
    support_conseq (map (hsubst (ren (+1))) cxt) phi ->
    support_conseq cxt <{forall phi}>.
Proof.
  intros cxt phi H1 M s a H2 i.
  apply H1.
  apply support_mult_hsubst_var.
  exact H2.
Qed.

Lemma support_conseq_Forall_E_rigid `{Signature} :
  forall cxt phi t,
    term_rigid t ->
    support_conseq cxt <{forall phi}> ->
    support_conseq cxt phi.|[t/].
Proof.
  intros cxt phi t H1 H2 M s a H3.
  specialize (H2 _ _ _ H3).
  rewrite support_Forall in H2.
  destruct (classic (consistent s)) as [[w H4]|H4].
  -
    specialize (H2 (referent t w a)).
    apply support_hsubst with
      (phi := phi)
      (s := s)
      (a := a)
      (sigma := (t .: ids))
      (w := w).
    +
      intros [|x']; easy.
    +
      assert (H5 :
        (fun x => referent ((t .: ids) x) w a) ==
        referent t w a .: a
      ).
      {
        intros [|x']; autosubst.
      }
      rewrite H5.
      exact H2.
  -
    apply state_eq_empty_state_iff_not_consistent in H4.
    rewrite H4.
    apply empty_state_property.
Qed.

Lemma support_conseq_Iexists_I `{S : Signature} :
  forall cxt phi t,
    term_rigid t ->
    support_conseq cxt phi.|[t .: ids] ->
    support_conseq cxt <{iexists phi}>.
Proof.
  intros cxt phi t H1 H2 M s a H3.
  specialize (H2 _ _ _ H3).
  destruct (classic (consistent s)) as [[w H4]|H4].
  -
    exists (referent t w a).
    apply support_hsubst with
      (phi := phi)
      (s := s)
      (a := a)
      (sigma := (t .: ids))
      (w := w)
      in H2.
    +
      assert (H5 :
        (fun x => referent ((t .: ids) x) w a) ==
        referent t w a .: a
      ).
      {
        intros [|x']; autosubst.
      }
      rewrite H5 in H2.
      exact H2.
    +
      intros [|x']; easy.
  -
    apply state_eq_empty_state_iff_not_consistent in H4.
    rewrite H4.
    apply empty_state_property.
Qed.

Lemma support_conseq_Iexists_E `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt <{iexists phi}> ->
    support_conseq (phi :: map (hsubst (ren (+1))) cxt) psi.|[ren (+1)] ->
    support_conseq cxt psi.
Proof.
  intros cxt phi psi H1 H2 M s a H3.
  specialize (H1 _ _ _ H3) as [i H4].
  enough (H6 : s, i .: a |= psi.|[ren (+1)]).
  {
    apply support_hsubst_var in H6.
    exact H6.
  }
  apply H2.
  apply mult_cons_I.
  -
    exact H4.
  -
    apply support_mult_hsubst_var.
    exact H3.
Qed.

Lemma support_conseq_Idisj_split `{S : Signature} :
  forall cxt phi psi chi,
    classical phi = true ->
    support_conseq cxt <{phi -> psi \\/ chi}> ->
    support_conseq cxt <{(phi -> psi) \\/ (phi -> chi)}>.
Proof.
Admitted.

Lemma support_conseq_Iexists_split `{S : Signature} :
  forall cxt phi psi,
    classical phi = true ->
    support_conseq cxt <{phi -> iexists psi}> ->
    let phi' :=
      phi.|[ren (+1)]
    in
    support_conseq cxt <{iexists phi' -> psi}>.
Proof.
Admitted.

Lemma support_conseq_KF `{S : Signature} :
  forall cxt phi,
    support_conseq cxt <{forall ~ ~ phi}> ->
    support_conseq cxt <{~ ~ forall phi}>.
Proof.
Admitted.

Lemma support_conseq_Forall_E_classical `{S : Signature} :
  forall cxt phi t,
    classical phi = true ->
    support_conseq cxt <{forall phi}> ->
    support_conseq cxt phi.|[t .: ids].
Proof.
  intros cxt phi t H1 H2 M s a H3.
  specialize (H2 _ _ _ H3).
  rewrite support_Forall in H2.
  apply classical_truth_conditional.
  -
    rewrite classical_hsubst.
    exact H1.
  -
    intros w H4.
    specialize (H2 (referent t w a)).
    apply truth_hsubst.
    apply truth_conditional_other_direction with
      (s := s).
    +
      assert (H5 :
        (fun x => referent ((t .: ids) x) w a) ==
        referent t w a .: a
      ).
      {
        intros [|x']; autosubst.
      }
      rewrite H5.
      exact H2.
    +
      exact H4.
Qed.

Lemma support_conseq_CRAA `{S : Signature} :
  forall cxt phi,
    classical phi = true ->
    support_conseq (<{~ phi}> :: cxt) (Bot 0) ->
    support_conseq cxt phi.
Proof.
  intros cxt phi H1 H2 M s a H3.
  apply classical_truth_conditional; try exact H1.
  intros w H4.
  apply NNPP.
  intros H5.
  rewrite <- truth_Neg in H5.
  enough (H6 : truth (Bot 0) w a).
  {
    rewrite truth_Bot in H6.
    exact H6.
  }
  apply H2.
  apply mult_cons_I.
  -
    exact H5.
  -
    eapply persistency_support_mult.
    +
      exact H3.
    +
      apply singleton_substate_iff.
      exact H4.
Qed.

Lemma support_conseq_CD `{S : Signature} :
  forall cxt phi psi,
    let psi' :=
      psi.|[ren (+1)]
    in
    support_conseq cxt <{forall phi \\/ psi'}> ->
    support_conseq cxt <{(forall phi) \\/ psi}>.
Proof.
  intros cxt phi psi psi' H1 M s a H2.
  destruct (classic (consistent s)) as [[w H3]|H3].
  -
    specialize (H1 _ _ _ H2).
    rewrite support_Forall in H1.
    assert (H4 :
      forall i,
        (s, i .: a |= phi) \/
        (s, a |= psi)
    ).
    {
      intros i.
      specialize (H1 i) as [H1|H1].
      -
        left.
        exact H1.
      -
        subst psi'.
        right.
        apply support_hsubst
          with (w := w)
          in H1.
        +
          exact H1.
        +
          easy.
    }
    rewrite support_Idisj.
    rewrite support_Forall.
    destruct (
      classic (exists i, ~ (s, i .: a |= phi))
    ) as [[i H5]|H5].
    +
      specialize (H4 i) as [H4|H4].
      *
        contradiction.
      *
        right.
        exact H4.
    +
      left.
      intros i.
      apply NNPP.
      intros H6.
      apply H5.
      exists i.
      exact H6.
  -
    apply state_eq_empty_state_iff_not_consistent in H3.
    rewrite H3.
    apply empty_state_property.
Qed.
