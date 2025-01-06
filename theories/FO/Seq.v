From InqLog.FO Require Export Truth.

(* whole section from inqbq_aiml *)

Inductive Seq `{Signature} :
  relation (list ((list nat)*form)) :=
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
          (pair ns <{forall phi}>) ::
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
          (pair ns <{iexists phi}>) ::
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
  (phi : ((list nat)*form)%type)
  (f : nat -> World)
  (a : assignment) : Prop :=
  mapping_state f (fst phi), a |= snd phi.

Definition satisfaction_conseq `{S : Signature} :
  relation (list ((list nat)*form)) :=
  fun Phi Psi =>
  forall `(M : @Model S) (f : nat -> World) (a : assignment),
    (
      forall phi,
        In phi Phi ->
        satisfaction phi f a
    ) ->
    exists psi,
      In psi Psi /\
      satisfaction psi f a.

Lemma satisfaction_conseq_empty `{Signature} :
  forall ls rs phi,
    In (pair nil phi) rs ->
    satisfaction_conseq ls rs.
Proof.
Admitted.

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
Admitted.

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
  assert (exists n, In n ns /\ f n = w) as [n [H6 H7]].
  {
    admit.
  }
  subst w.
  specialize (H2 n H6 M f a H3) as [psi [H7 H8]].
  destruct H7 as [H7|H7].
  +
    subst psi.
    asimpl in H8.
    apply H8.
    destruct (World_deceq (f n) (f n)) as [H9|H9]; easy.
  +
    assert (H9 : psi = pair ns (Pred p args)).
    {
      apply NNPP.
      intros H9.
      apply H4.
      eexists; repeat split; eassumption.
    }
    subst psi.
    apply H8.
    exact H5.
Admitted.

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
Admitted.

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
Admitted.

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
      apply H6.
      --
         admit.
      --
         exact H8.
    *
      apply H5.
      exact H9.
  +
    eexists; split; eassumption.
Admitted.

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
Admitted.

Lemma satisfaction_conseq_Forall_l `{Signature} :
  forall ns ls rs phi t,
    In (pair ns <{forall phi}>) ls ->
    rigid_term t ->
    satisfaction_conseq
    (
      (pair ns phi.|[t/]) ::
      (pair ns <{forall phi}>) ::
      ls
    )
    (
      rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
Admitted.

Lemma satisfaction_conseq_Iexists_r `{Signature} :
  forall ns ls rs phi t,
    In (pair ns <{iexists phi}>) rs ->
    rigid_term t ->
    satisfaction_conseq ls
    (
      (pair ns phi.|[t/]) ::
      (pair ns <{iexists phi}>) ::
      rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
Admitted.

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
Admitted.

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
