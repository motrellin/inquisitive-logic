From InqLog.FO Require Export Truth.

(* whole section from inqbq_aiml *)

Definition label : Type := list nat.
Definition lb_form `{Signature} : Type := (list nat)*form.

Inductive Seq `{Signature} :
  relation (list lb_form) :=
  | Seq_empty :
      forall ls rs phi,
        In (pair nil phi) rs ->
        Seq ls rs
  | Seq_id :
      forall ns ls rs p args,
        In (pair ns (Pred p args)) ls ->
        In (pair ns (Pred p args)) rs ->
        Seq ls rs
  | Seq_Bot_l :
      forall n ns ls rs x,
        In (pair ns (Bot x)) ls ->
        In n ns ->
        Seq ls rs
  | Seq_Pred_r :
      forall ns ls rs p args,
        In (pair ns (Pred p args)) rs ->
        (forall n,
          In n ns ->
          Seq ls ((pair (n :: nil) (Pred p args)) :: rs)
        ) ->
        Seq ls rs
  | Seq_Pred_l :
      forall ns1 ns2 ls rs p args,
        In (pair ns1 (Pred p args)) ls ->
        (forall n,
          In n ns2 ->
          In n ns1
        ) ->
        Seq ((pair ns2 (Pred p args)) :: ls) rs ->
        Seq ls rs
  | Seq_Impl_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi -> psi}>) rs ->
        (forall ns',
          (forall n,
            In n ns' ->
            In n ns
          ) ->
          Seq ((pair ns' phi) :: ls) ((pair ns' psi) :: rs)
        ) ->
        Seq ls rs
  | Seq_Impl_l :
      forall ns1 ns2 ls rs phi psi,
        In (pair ns1 <{phi -> psi}>) ls ->
        (forall n,
          In n ns2 ->
          In n ns1
        ) ->
        Seq ls ((pair ns2 phi) :: rs) ->
        Seq ((pair ns2 psi) :: ls) rs ->
        Seq ls rs
  | Seq_Conj_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi /\ psi}>) rs ->
        Seq ls ((pair ns phi) :: rs) ->
        Seq ls ((pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Conj_l :
      forall ns ls rs phi psi,
        In (pair ns <{phi /\ psi}>) ls ->
        Seq ((pair ns phi) :: (pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Idisj_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi \\/ psi}>) rs ->
        Seq ls ((pair ns phi) :: (pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Idisj_l :
      forall ns ls rs phi psi,
        In (pair ns <{phi \\/ psi}>) ls ->
        Seq ((pair ns phi) :: ls) rs ->
        Seq ((pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Forall_r :
      forall ns ls rs phi,
        In (pair ns <{forall phi}>) rs ->
        Seq
        (
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
        )
        (
          (pair ns phi) ::
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
        ) ->
        Seq ls rs
  | Seq_Forall_l :
      forall ns ls rs phi t,
        In (pair ns <{forall phi}>) ls ->
        rigid_term t ->
        Seq
        (
          (pair ns phi.|[t/]) ::
          ls
        )
        (
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_r :
      forall ns ls rs phi t,
        In (pair ns <{iexists phi}>) rs ->
        rigid_term t ->
        Seq ls
        (
          (pair ns phi.|[t/]) ::
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_l :
      forall ns ls rs phi,
        In (pair ns <{iexists phi}>) ls ->
        Seq
        (
          (pair ns phi) ::
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
        )
        (
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
        ) ->
        Seq ls rs.

Proposition prop_4_6 `{Signature} :
  forall phi ns1 ns2 ls rs,
  In (pair ns1 phi) ls ->
  In (pair ns2 phi) rs ->
  (forall n, In n ns2 -> In n ns1) ->
  Seq ls rs.
Proof with (
  try (
    eapply in_map_iff;
    eexists;
    split;
    try reflexivity;
    try eassumption);
  try reflexivity;
  try (left; reflexivity);
  try (right; eassumption);
  try (right; left; reflexivity);
  eauto
).
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros ns1 ns2 ls rs H1 H2 H3.
  -
    eapply Seq_Pred_l...
    eapply Seq_id...
  -
    destruct ns2 as [|n ns2'].
    +
      eapply Seq_empty...
    +
      eapply Seq_Bot_l.
      *
        exact H1.
      *
        apply H3.
        left.
        reflexivity.
  -
    eapply Seq_Impl_r...
    intros ns3 H4.
    eapply Seq_Impl_l with (ns2 := ns3)...
    +
      eapply IH1...
    +
      eapply IH2...
  -
    eapply Seq_Conj_l...
    eapply Seq_Conj_r...
    +
      eapply IH1...
    +
      eapply IH2...
  -
    eapply Seq_Idisj_r...
    eapply Seq_Idisj_l...
    +
      eapply IH1...
    +
      eapply IH2...
  -
    eapply Seq_Forall_r...
    eapply Seq_Forall_l with (t := Var 0)...
    asimpl.
    eapply IH1...
  -
    eapply Seq_Iexists_l...
    eapply Seq_Iexists_r with (t := Var 0)...
    asimpl.
    eapply IH1...
Qed.

Example ex_4_7 `{Signature} :
  forall ns phi psi,
    Seq
    ((pair ns <{iexists phi}>) :: nil)
    ((pair ns <{iexists ~ psi -> phi}>) :: nil).
Proof with (
  try (right; left; autosubst);
  try (left; autosubst);
  try easy
).
  intros ns1 phi psi.
  eapply Seq_Iexists_l...
  eapply Seq_Iexists_r with (t := Var 0)...
  eapply Seq_Impl_r...
  intros ns' H1.
  eapply prop_4_6...
Qed.

Example ex_4_8 `{Signature} :
  forall ns phi psi,
    Seq
    ((pair ns <{(forall phi) \\/ psi}>) :: nil)
    ((pair ns (Forall (Idisj phi psi.|[ren (+1)]))) :: nil).
Proof with (
  try (left; autosubst);
  try (right; left; autosubst);
  try easy
).
  intros ns phi psi.
  eapply Seq_Forall_r...
  eapply Seq_Idisj_l...
  all: eapply Seq_Idisj_r...
  -
    eapply Seq_Forall_l with (t := Var 0)...
    eapply prop_4_6...
  -
    eapply prop_4_6...
Qed.

Definition satisfaction
  `{Model}
  (phi : lb_form)
  (f : nat -> World)
  (a : assignment) : Prop :=
  mapping_state f (fst phi), a |= snd phi.

Lemma satisfaction_subst `{Model} :
  forall phi f a sigma w,
    (forall x, rigid_term (sigma x)) ->
    satisfaction phi f (fun x => referent (sigma x) w a) <->
    satisfaction (pair (fst phi) (snd phi).|[sigma]) f a.
Proof.
  intros.
  apply support_subst.
  exact H1.
Qed.

Lemma satisfaction_subst_var `{Model} :
  forall phi f a sigma,
    satisfaction phi f (sigma >>> a) <->
    satisfaction (pair (fst phi) (snd phi).|[ren sigma]) f a.
Proof.
  intros.
  apply support_subst_var.
Qed.

Definition satisfaction_forall
  `{Model}
  (Phi : list lb_form)
  (f : nat -> World)
  (a : assignment) :
  Prop :=

  forall phi,
    In phi Phi ->
    satisfaction phi f a.

Lemma satisfaction_forall_nil `{Model} :
  forall f a,
    satisfaction_forall nil f a.
Proof.
  easy.
Qed.

Lemma satisfaction_forall_cons `{Model} :
  forall phi Phi' f a,
    satisfaction_forall (phi :: Phi') f a <->
    satisfaction phi f a /\
    satisfaction_forall Phi' f a.
Proof.
  intros phi Phi' f a.
  split.
  -
    intros H1.
    split.
    +
      apply H1.
      left.
      reflexivity.
    +
      intros psi H2.
      apply H1.
      right.
      exact H2.
  -
    intros [H1 H2] psi [H3|H3].
    +
      subst psi.
      exact H1.
    +
      apply H2.
      exact H3.
Qed.

Lemma satisfaction_forall_subst_var `{Model} :
  forall Phi f a sigma,
    satisfaction_forall Phi f (sigma >>> a) <->
    satisfaction_forall (map (fun phi => pair (fst phi) (snd phi).|[ren sigma]) Phi) f a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    easy.
  -
    simpl.
    split.
    all: intros H2.
    all: apply satisfaction_forall_cons.
    all: apply satisfaction_forall_cons in H2 as [H2 H3].
    all: split.
    all: try (apply IH; exact H3).
    +
      apply satisfaction_subst_var in H2.
      assumption.
    +
      apply satisfaction_subst_var.
      assumption.
Qed.

Definition satisfaction_exists
  `{Model}
  (Phi : list lb_form)
  (f : nat -> World)
  (a : assignment) :
  Prop :=

  exists phi,
    In phi Phi /\
    satisfaction phi f a.

Lemma satisfaction_exists_nil `{Model} :
  forall f a,
    ~ satisfaction_exists nil f a.
Proof.
  intros f a [phi [H1 H2]].
  contradiction.
Qed.

Lemma satisfaction_exists_cons `{Model} :
  forall phi Phi' f a,
    satisfaction_exists (phi :: Phi') f a <->
    satisfaction phi f a \/
    satisfaction_exists Phi' f a.
Proof.
  intros phi Phi' f a.
  split.
  -
    intros [psi [[H2|H2] H3]].
    +
      subst psi.
      left.
      exact H3.
    +
      right.
      exists psi; split; assumption.
  -
    intros [H1|[psi [H2 H3]]].
    +
      exists phi.
      split.
      *
        left.
        reflexivity.
      *
        exact H1.
    +
      exists psi; split.
      *
        right; assumption.
      *
        exact H3.
Qed.

Lemma satisfaction_exists_subst_var `{Model} :
  forall Phi s a sigma,
    satisfaction_exists Phi s (sigma >>> a) <->
    satisfaction_exists (map (fun phi => pair (fst phi) (snd phi).|[ren sigma]) Phi) s a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    firstorder.
  -
    split.
    all: simpl.
    all: intros H2.
    all: apply satisfaction_exists_cons.
    all: apply satisfaction_exists_cons in H2 as [H2|H2].
    all: try (right; eapply IH; eassumption).
    +
      apply satisfaction_subst_var in H2.
      left.
      exact H2.
    +
      left.
      apply satisfaction_subst_var.
      exact H2.
Qed.

Definition satisfaction_conseq `{S : Signature} :
  relation (list lb_form) :=
  fun Phi Psi =>
  forall `(M : @Model S) (f : nat -> World) (a : assignment),
    satisfaction_forall Phi f a ->
    satisfaction_exists Psi f a.

Lemma satisfaction_conseq_empty `{Signature} :
  forall ls rs phi,
    In (pair nil phi) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros ls rs phi H1.
  intros M f a H2.
  eexists; split; try exact H1.
  apply empty_state_property.
Qed.

Lemma satisfaction_conseq_id `{Signature} :
      forall ns ls rs p args,
        In (pair ns (Pred p args)) ls ->
        In (pair ns (Pred p args)) rs ->
        satisfaction_conseq ls rs.
Proof.
  intros ns ls rs p args H1 H2.
  intros M f a H3.
  eexists.
  split.
  +
    exact H2.
  +
    apply H3.
    exact H1.
Qed.

Lemma satisfaction_conseq_Bot_l `{Signature} :
  forall n ns ls rs x,
    In (pair ns (Bot x)) ls ->
    In n ns ->
    satisfaction_conseq ls rs.
Proof.
  intros n ns ls rs ? H1 H2.
  intros M f a H3.
  specialize (H3 _ H1 (f n)).
  simpl in H3.
  unfold mapping_state in H3.
  eapply in_map in H2.
  eapply In_iff_inb in H2.
  rewrite H3 in H2.
  discriminate.
Qed.

Lemma satisfaction_conseq_Pred_r `{Signature} :
  forall ns ls rs p args,
    In (pair ns (Pred p args)) rs ->
    (forall n,
      In n ns ->
      satisfaction_conseq ls
      (
        (pair (n :: nil) (Pred p args)) :: rs
      )
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs p args H1 H2.
  intros M f a H3.
  destruct (classic (exists psi, psi <> (pair ns (Pred p args)) /\ In psi rs /\ satisfaction psi f a)) as [H4|H4].
  {
    destruct H4 as [psi [_ [H4 H5]]].
    exists psi.
    split; assumption.
  }
  eexists.
  split; try exact H1.
  intros w H5.
  apply In_iff_inb in H5 as H6.
  simpl in H6.
  apply in_map_iff in H6 as [n [H6 H7]].
  subst w.
  specialize (H2 n H7 M f a H3) as [psi [H8 H9]].
  destruct H8 as [H8|H8].
  +
    subst psi.
    apply H9.
    asimpl.
    destruct (World_deceq (f n) (f n)) as [HA|HA]; easy.
  +
    assert (HA : psi = pair ns (Pred p args)).
    {
      apply NNPP.
      intros HA.
      apply H4.
      eexists; repeat split; eassumption.
    }
    subst psi.
    apply H9.
    exact H5.
Qed.

Lemma satisfaction_conseq_Pred_l `{Signature} :
  forall ns1 ns2 ls rs p args,
    In (pair ns1 (Pred p args)) ls ->
    (forall n,
      In n ns2 ->
      In n ns1
    ) ->
    satisfaction_conseq ((pair ns2 (Pred p args)) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros ns1 ns2 ls rs p args H1 H2 H3.
  intros M f a H4.
  apply H3.
  intros phi [H5|H5].
  -
    subst phi.
    apply H4 in H1.
    eapply persistency.
    +
      exact H1.
    +
      apply substate_mapping_state.
      exact H2.
  -
    apply H4.
    exact H5.
Qed.

Lemma satisfaction_conseq_Impl_r `{Signature} :
  forall ns ls rs phi psi,
    In (pair ns <{phi -> psi}>) rs ->
    (forall ns',
      (forall n,
        In n ns' ->
        In n ns
      ) ->
      satisfaction_conseq
      (
        (pair ns' phi) :: ls
      )
      (
        (pair ns' psi) :: rs
      )
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns1 ls rs phi psi H1 H2.
  intros M f a H3.
  destruct (
    classic (
      exists chi,
        chi <> (pair ns1 <{phi -> psi}>) /\
        In chi rs /\
        satisfaction chi f a
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    exists chi.
    split; assumption.
  }
  eexists; split; try exact H1.

  intros t H5 H6.
  simpl in H5.

  apply substate_mapping_state_iff in H5 as [ns2 [H7 H8]].
  rewrite H7 in *; clear H7.

  specialize (H2 ns2 H8).
  assert (H9 :
    forall chi,
      In chi ((pair ns2 phi) :: ls) ->
      satisfaction chi f a
  ).
  {
    intros chi [H9|H9].
    -
      subst chi.
      exact H6.
    -
      apply H3.
      exact H9.
  }
  specialize (H2 _ _ _ H9) as [chi [[HA|HA] HB]].
  -
    subst chi.
    exact HB.
  -
    assert (HC : chi = pair ns1 <{phi -> psi}>).
    {
      apply NNPP.
      intros HC.
      apply H4.
      exists chi.
      easy.
    }
    subst chi.
    asimpl in HB.
    apply HB.
    +
      apply substate_mapping_state.
      exact H8.
    +
      exact H6.
Qed.

Lemma satisfaction_conseq_Impl_l `{Signature} :
  forall ns1 ns2 ls rs phi psi,
    In (pair ns1 <{phi -> psi}>) ls ->
    (forall n,
      In n ns2 ->
      In n ns1
    ) ->
    satisfaction_conseq ls ((pair ns2 phi) :: rs) ->
    satisfaction_conseq ((pair ns2 psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros ns1 ns2 ls rs phi psi H1 H2 H3 H4.
  intros M f a H5.
  specialize (H5 _ H1) as H6.
  specialize (H3 _ _ _ H5) as [chi [[H7|H7] H8]].
  +
    subst chi.
    apply H4.
    intros chi [H9|H9].
    *
      subst chi.
      asimpl in H6.
      apply H6.
      --
         apply substate_mapping_state.
         exact H2.
      --
         exact H8.
    *
      apply H5.
      exact H9.
  +
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Conj_r `{Signature} :
  forall ns ls rs phi psi,
    In (pair ns <{phi /\ psi}>) rs ->
    satisfaction_conseq ls ((pair ns phi) :: rs) ->
    satisfaction_conseq ls ((pair ns psi) :: rs) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi psi H1 H2 H3.
  intros M f a H4.
  specialize (H2 _ _ _ H4) as [[ns2 psi1] [[H5|H5] H6]].
  +
    injection H5; intros; subst ns2 psi1; clear H5.
    specialize (H3 _ _ _ H4) as [[ns3 psi2] [[H7|H7] H8]].
    *
      injection H7; intros; subst ns3 psi2; clear H7.
      eexists.
      split.
      --
         exact H1.
      --
         split; assumption.
    *
      eexists; split; eassumption.
  +
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Conj_l `{Signature} :
  forall ns ls rs phi psi,
    In (pair ns <{phi /\ psi}>) ls ->
    satisfaction_conseq
    (
      (pair ns phi) :: (pair ns psi) :: ls
    ) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi psi H1 H2.
  intros M f a H3.
  specialize (H3 _ H1) as H4.
  destruct H4 as [H4 H5].
  apply H2.
  intros chi [H6|[H6|H6]].
  +
    subst chi.
    exact H4.
  +
    subst chi.
    exact H5.
  +
    apply H3.
    exact H6.
Qed.

Lemma satisfaction_conseq_Idisj_r `{Signature} :
  forall ns ls rs phi psi,
    In (pair ns <{phi \\/ psi}>) rs ->
    satisfaction_conseq ls
    (
      (pair ns phi) :: (pair ns psi) :: rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi psi H1 H2.
  intros M f a H3.
  specialize (H2 _ _ _ H3) as [chi [H4 H5]].
  destruct H4 as [H4|[H4|H4]].
  -
    subst chi.
    eexists; split; try exact H1.
    left.
    exact H5.
  -
    subst chi.
    eexists; split; try exact H1.
    right.
    exact H5.
  -
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Idisj_l `{Signature} :
  forall ns ls rs phi psi,
    In (pair ns <{phi \\/ psi}>) ls ->
    satisfaction_conseq ((pair ns phi) :: ls) rs ->
    satisfaction_conseq ((pair ns psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi psi H1 H2 H3.
  intros M f a H4.
  apply H4 in H1 as H5.
  destruct H5 as [H5|H5].
  -
    apply H2.
    intros chi [H6|H6].
    +
      subst chi.
      exact H5.
    +
      apply H4.
      exact H6.
  -
    apply H3.
    intros chi [H6|H6].
    +
      subst chi.
      exact H5.
    +
      apply H4.
      exact H6.
Qed.

Lemma satisfaction_conseq_Forall_r `{Signature} :
  forall ns ls rs phi,
    In (pair ns <{forall phi}>) rs ->
    satisfaction_conseq
    (
      map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
    )
    (
      (pair ns phi) ::
      map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi H1 H2.
  intros M f a H3.

  destruct (
    classic (
      exists chi,
        chi <> (pair ns <{forall phi}>) /\
        In chi rs /\
        satisfaction chi f a
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    exists chi; split; assumption.
  }
  eexists; split; try exact H1.
  intros i.
  simpl.

  eapply satisfaction_exists_cons with
    (f := f)
    (a := i .: a)
    in H2 as [H2|H2].
  -
    exact H2.
  -
    destruct H2 as [psi [H5 H6]].
    apply in_map_iff in H5 as [chi [H7 H8]].
    subst psi.
    apply satisfaction_subst_var in H6.

    assert (H9 : chi = pair ns (Forall phi)).
    {
      apply NNPP.
      intros H9.
      apply H4; eexists; repeat split; eassumption.
    }
    subst chi.
    apply H6.
  -
    apply satisfaction_forall_subst_var.
    exact H3.
Qed.

Lemma satisfaction_conseq_Forall_l `{Signature} :
  forall ns ls rs phi t,
    In (pair ns <{forall phi}>) ls ->
    rigid_term t ->
    satisfaction_conseq
    (
      (pair ns phi.|[t/]) ::
      ls
    )
    (
      rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi t H1 H2 H3.
  intros M f a H4.
  specialize (H4 _ H1) as H5.

  apply H3.
  intros psi [H6|H6].
  -
    subst psi.
    destruct ns as [|n ns'].
    +
      apply empty_state_property.
    +
      asimpl.
      asimpl in H5.
      specialize (H5 (referent t (f n) a)).

      eapply support_subst with
        (sigma := t .: ids)
        (w := f n).
      *
        intros [|]; easy.
      *
        assert (H6 :
          (fun x => referent ((t .: ids) x) (f n) a) =
          referent t (f n) a .: a
        ).
        {
          apply functional_extensionality.
          intros [|x']; autosubst.
        }
        rewrite H6.
        exact H5.
  -
    apply H4.
    exact H6.
Qed.

Lemma satisfaction_conseq_Iexists_r `{Signature} :
  forall ns ls rs phi t,
    In (pair ns <{iexists phi}>) rs ->
    rigid_term t ->
    satisfaction_conseq ls
    (
      (pair ns phi.|[t/]) ::
      rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi t H1 H2 H3.
  intros M f a H4.
  specialize (H3 _ _ _ H4) as H5.
  apply satisfaction_exists_cons in H5 as [H5|H5].
  -
    eexists; split; try exact H1.
    destruct ns as [|n ns'].
    +
      apply empty_state_property.
    +
      exists (referent t (f n) a).
      asimpl.
      asimpl in H5.
      eapply support_subst with
        (sigma := t .: ids)
        in H5.
      *
        assert (H6 :
          referent t (f n) a .: a =
          fun x => referent ((t .: ids) x) (f n) a
        ).
        {
          apply functional_extensionality.
          intros [|x']; reflexivity.
        }
        rewrite H6.
        exact H5.
      *
        intros [|x']; easy.
  -
    exact H5.
Qed.

Lemma satisfaction_conseq_Iexists_l `{Signature} :
  forall ns ls rs phi,
    In (pair ns <{iexists phi}>) ls ->
    satisfaction_conseq
    (
      (pair ns phi) ::
      map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
    )
    (
      map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros ns ls rs phi H1 H2.
  intros M f a H3.
  specialize (H3 _ H1) as H4.
  asimpl in H4.
  destruct H4 as [i H4].
  specialize (H2 M f (i .: a)).
  apply satisfaction_exists_subst_var in H2.
  -
    exact H2.
  -
    apply satisfaction_forall_cons.
    split.
    +
      exact H4.
    +
      apply satisfaction_forall_subst_var.
      exact H3.
Qed.

Theorem soundness `{Signature} :
  forall Phi Psi,
    Seq Phi Psi ->
    satisfaction_conseq Phi Psi.
Proof.
  induction 1 as
  [ls rs phi H1 (* Seq_empty *)
  |ns ls rs p args H1 H2 (* Seq_id *)
  |ns ls rs x H1 (* Seq_Bot_l *)
  |ns ls rs p args H1 H2 IH1 (* Seq_Pred_r *)
  |ns1 ns2 ls rs p args H1 H2 H3 IH1 (* Seq_Pred_l *)
  |ns ls rs phi psi H1 H2 IH1 (* Seq_Impl_r *)
  |ns1 ns2 ls rs phi psi H1 H2 H3 IH1 H4 IH2 (* Seq_Impl_l *)
  |ns ls rs phi psi H1 H2 IH1 H3 IH2 (* Seq_Conj_r *)
  |ns ls rs phi psi H1 H2 IH1 (* Seq_Conj_l *)
  |ns ls rs phi psi H1 H2 IH1 (* Seq_Idisj_r *)
  |ns ls rs phi psi H1 H2 IH1 H3 IH2 (* Seq_Idisj_l *)
  |ns ls rs phi H1 H2 IH1 (* Seq_Forall_r *)
  |ns ls rs phi t H1 H2 H3 IH1 (* Seq_Forall_l *)
  |ns ls rs phi t H1 H2 H3 IH1 (* Seq_Iexists_r *)
  |ns ls rs phi H1 H2 IH1 (* Seq_Iexists_l *)].
  all: eauto using
    satisfaction_conseq_empty,
    satisfaction_conseq_id,
    satisfaction_conseq_Bot_l,
    satisfaction_conseq_Pred_r,
    satisfaction_conseq_Pred_l,
    satisfaction_conseq_Impl_r,
    satisfaction_conseq_Impl_l,
    satisfaction_conseq_Conj_r,
    satisfaction_conseq_Conj_l,
    satisfaction_conseq_Idisj_r,
    satisfaction_conseq_Idisj_l,
    satisfaction_conseq_Forall_r,
    satisfaction_conseq_Forall_l,
    satisfaction_conseq_Iexists_r,
    satisfaction_conseq_Iexists_l.
Qed.

Print Assumptions soundness.
