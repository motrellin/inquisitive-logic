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
