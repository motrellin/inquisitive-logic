From InqLog.FO Require Export Truth.

(* whole section from inqbq_aiml *)

(** * Defining the Sequent Calculus

   For the sequent calculus introduced by Litak/Sano, we
   first the define the notion of _labelled formulas_. A
   labelled formel is a pair consisting of a list of
   natural numbers and a formula.

   We will frequently use the notions of [In_eq] and
   [In_sublist], as the original paper uses sets to define
   labels.
 *)

Definition label : Type := list nat.
Definition lb_form `{Signature} : Type := (list nat)*form.

(**
   Now, we are in a position to define the rules of the
   Sequent Calculus in Coq. For this, we define [Seq] as a
   [relation] on [list]s of labelled forms.
 *)

Inductive Seq `{Signature} :
  relation (list lb_form) :=
  (**
     As we allow arbitrary lists of natural numbers as
     labels, we add an extra rule to capture this:
     [Seq_empty]. By intuition, these labels correspondent
     to states, e.g. the empty list [nil] corresponds to the
     empty state. By this, we want to be in a position to
     derive a formula with an empty label.
   *)
  | Seq_empty :
      forall ls rs phi,
        In (pair nil phi) rs ->
        Seq ls rs
  (**
     The following rules correspond to the original sequent
     calculus.
   *)
  | Seq_id :
      forall ls rs ns1 ns2 p args,
        In (pair ns1 (Pred p args)) ls ->
        In (pair ns2 (Pred p args)) rs ->
        In_eq ns1 ns2 ->
        Seq ls rs
  | Seq_Bot_l :
      forall ls rs n ns x,
        In (pair ns (Bot x)) ls ->
        In n ns ->
        Seq ls rs
  | Seq_Pred_r :
      forall ls rs ns p args,
        In (pair ns (Pred p args)) rs ->
        (forall n,
          In n ns ->
          Seq ls ((pair (n :: nil) (Pred p args)) :: rs)
        ) ->
        Seq ls rs
  | Seq_Pred_l :
      forall ls rs ns1 ns2 p args,
        In (pair ns1 (Pred p args)) ls ->
        In_sublist ns2 ns1 ->
        Seq ((pair ns2 (Pred p args)) :: ls) rs ->
        Seq ls rs
  | Seq_Impl_r :
      forall ls rs ns phi psi,
        In (pair ns <{phi -> psi}>) rs ->
        (forall ns',
          In_sublist ns' ns ->
          Seq ((pair ns' phi) :: ls) ((pair ns' psi) :: rs)
        ) ->
        Seq ls rs
  | Seq_Impl_l :
      forall ls rs ns1 ns2 phi psi,
        In (pair ns1 <{phi -> psi}>) ls ->
        In_sublist ns2 ns1 ->
        Seq ls ((pair ns2 phi) :: rs) ->
        Seq ((pair ns2 psi) :: ls) rs ->
        Seq ls rs
  | Seq_Conj_r :
      forall ls rs ns phi psi,
        In (pair ns <{phi /\ psi}>) rs ->
        Seq ls ((pair ns phi) :: rs) ->
        Seq ls ((pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Conj_l :
      forall ls rs ns phi psi,
        In (pair ns <{phi /\ psi}>) ls ->
        Seq ((pair ns phi) :: (pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Idisj_r :
      forall ls rs ns phi psi,
        In (pair ns <{phi \\/ psi}>) rs ->
        Seq ls ((pair ns phi) :: (pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Idisj_l :
      forall ls rs ns phi psi,
        In (pair ns <{phi \\/ psi}>) ls ->
        Seq ((pair ns phi) :: ls) rs ->
        Seq ((pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Forall_r :
      forall ls rs ns phi,
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
      forall ls rs ns phi t,
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
      forall ls rs ns phi t,
        In (pair ns <{iexists phi}>) rs ->
        rigid_term t ->
        Seq ls
        (
          (pair ns phi.|[t/]) ::
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_l :
      forall ls rs ns phi,
        In (pair ns <{iexists phi}>) ls ->
        Seq
        (
          (pair ns phi) ::
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
        )
        (
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
        ) ->
        Seq ls rs
  (**
     In addition, we add the cut elimination rule to our
     calculus, which is shown to be admissible by Litak/Sano.
   *)
  | Seq_cut :
      forall ls1 ls2 ls rs1 rs2 rs ns phi,
        In_eq ls (ls1 ++ ls2) ->
        In_eq rs (rs1 ++ rs2) ->
        Seq ls1 ((pair ns phi) :: rs1) ->
        Seq ((pair ns phi) :: ls2) rs2 ->
        Seq ls rs.

(** ** Properties of [Seq] *)

Proposition prop_4_6 `{Signature} :
  forall ls rs ns1 ns2 phi,
  In (pair ns1 phi) ls ->
  In (pair ns2 phi) rs ->
  In_sublist ns2 ns1 ->
  Seq ls rs.
Proof.
  intros *.
  revert ls rs ns1 ns2.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros * H1 H2 H3.
  -
    eapply Seq_Pred_l.
    +
      exact H1.
    +
      exact H3.
    +
      eapply Seq_id.
      *
        left; reflexivity.
      *
        exact H2.
      *
        reflexivity.
  -
    destruct ns2 as [|n ns2'].
    +
      eapply Seq_empty.
      exact H2.
    +
      eapply Seq_Bot_l.
      *
        exact H1.
      *
        apply H3.
        left; reflexivity.
  -
    eapply Seq_Impl_r.
    +
      exact H2.
    +
      intros ns3 H4.
      eapply Seq_Impl_l.
      *
        right; exact H1.
      *
        etransitivity; eassumption.
      *
        eapply IH1.
        --
           left; reflexivity.
        --
           left; reflexivity.
        --
           reflexivity.
      *
        eapply IH2.
        --
           left; reflexivity.
        --
           left; reflexivity.
        --
           reflexivity.
  -
    eapply Seq_Conj_l.
    +
      exact H1.
    +
      eapply Seq_Conj_r.
      *
        exact H2.
      *
        eapply IH1.
        --
           left; reflexivity.
        --
           left; reflexivity.
        --
           exact H3.
      *
        eapply IH2.
        --
           right; left; reflexivity.
        --
           left; reflexivity.
        --
           exact H3.
  -
    eapply Seq_Idisj_r.
    +
      exact H2.
    +
      eapply Seq_Idisj_l.
      *
        exact H1.
      *
        eapply IH1.
        --
           left; reflexivity.
        --
           left; reflexivity.
        --
           exact H3.
      *
        eapply IH2.
        --
           left; reflexivity.
        --
           right; left; reflexivity.
        --
           exact H3.
  -
    eapply Seq_Forall_r.
    +
      exact H2.
    +
      eapply Seq_Forall_l with (t := Var 0).
      *
        apply in_map_iff.
        exists (pair ns1 <{forall phi1}>).
        easy.
      *
        exact I.
      *
        eapply IH1.
        --
           left; autosubst.
        --
           left; reflexivity.
        --
           exact H3.
  -
    eapply Seq_Iexists_l.
    +
      exact H1.
    +
      eapply Seq_Iexists_r with (t := Var 0).
      *
        apply in_map_iff.
        exists (pair ns2 <{iexists phi1}>).
        easy.
      *
        exact I.
      *
        eapply IH1.
        --
           left; reflexivity.
        --
           left; autosubst.
        --
           exact H3.
Qed.

(** ** Some example derivations *)

Example ex_4_5 `{Signature} :
  forall ns n p args,
    In n ns ->
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
    left.
    reflexivity.
  -
    intros n2 [H2|H2].
    +
      congruence.
    +
      contradiction.
  -
    apply Seq_Impl_r with
      (ns := n1 :: nil)
      (phi := Pred p args)
      (psi := Bot 0).
    +
      left.
      reflexivity.
    +
      intros ns2 H2.
      apply In_sublist_singleton in H2 as [H2|H2]; try decide equality.
      *
        apply Seq_id with
          (ns1 := ns2)
          (ns2 := n1 :: nil)
          (p := p)
          (args := args).
        --
           left.
           reflexivity.
        --
           right.
           right.
           left.
           reflexivity.
        --
           exact H2.
      *
        subst ns2.
        apply Seq_empty with
          (phi := Bot 0).
        left.
        reflexivity.
  -
    apply Seq_Bot_l with
      (n := n1)
      (ns := n1 :: nil)
      (x := 0).
    +
      left.
      reflexivity.
    +
      left.
      reflexivity.
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

(** * Corresponding semantic

   We need a notion of [satisfaction] in order to
   understand the sequent calculus. We want to interpret
   a labelled formula in a Model by a _mapping function_ [f]
   and a variable assignment [a].

   Note, that we used a different argument order as for the
   [support] relation. By this, we can use some notions of
   the standard library more readable.
 *)

Definition satisfaction
  `{Model}
  (f : nat -> World)
  (a : assignment)
  (phi : lb_form) : Prop :=
  mapping_state f (fst phi), a |= snd phi.

Lemma satisfaction_subst `{Model} :
  forall phi f a sigma w,
    (forall x, rigid_term (sigma x)) ->
    satisfaction f (fun x => referent (sigma x) w a) phi <->
    satisfaction f a (pair (fst phi) (snd phi).|[sigma]).
Proof.
  intros.
  apply support_subst.
  exact H1.
Qed.

Lemma satisfaction_subst_var `{Model} :
  forall phi f a sigma,
    satisfaction f (sigma >>> a) phi <->
    satisfaction f a (pair (fst phi) (snd phi).|[ren sigma]).
Proof.
  intros.
  apply support_subst_var.
Qed.

(** ** [satisfaction_forall] *)

Definition satisfaction_forall
  `{Model}
  (Phi : list lb_form)
  (f : nat -> World)
  (a : assignment) :
  Prop :=
  List.Forall (satisfaction f a) Phi.

Arguments satisfaction_forall _ /.

Instance satisfaction_forall_Proper `{Model} :
  Proper (In_eq ==> eq ==> eq ==> iff) satisfaction_forall.
Proof.
  intros Phi1 Phi2 H1 f1 f2 H2 a1 a2 H3.
  subst.
  split.
  all: intros H4.
  all: apply Forall_forall.
  all: intros phi H5.
  all: eapply Forall_forall in H4.
  all: try apply H1.
  all: eassumption.
Qed.

Lemma satisfaction_forall_subst_var `{Model} :
  forall Phi f a sigma,
    satisfaction_forall Phi f (sigma >>> a) <->
    satisfaction_forall (map (fun phi => pair (fst phi) (snd phi).|[ren sigma]) Phi) f a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    simpl.
    easy.
  -
    simpl.
    split.
    all: intros H2.
    all: apply Forall_cons_iff.
    all: apply Forall_cons_iff in H2 as [H2 H3].
    all: split.
    all: try (apply IH; exact H3).
    +
      apply satisfaction_subst_var in H2.
      assumption.
    +
      apply satisfaction_subst_var.
      assumption.
Qed.

(** ** [satisfaction_exists] *)

Definition satisfaction_exists
  `{Model}
  (Phi : list lb_form)
  (f : nat -> World)
  (a : assignment) :
  Prop :=

  List.Exists (satisfaction f a) Phi.

Arguments satisfaction_exists _ /.

Instance satisfaction_exists_Proper `{Model} :
  Proper (In_eq ==> eq ==> eq ==> iff) satisfaction_exists.
Proof.
  intros Phi1 Phi2 H1 f1 f2 H2 a1 a2 H3.
  subst.
  split.
  all: intros H4.
  all: apply Exists_exists in H4 as [phi [H4 H5]].
  all: apply Exists_exists.
  all: exists phi.
  all: split.
  all: try apply H1.
  all: assumption.
Qed.

Lemma satisfaction_exists_subst_var `{Model} :
  forall Phi s a sigma,
    satisfaction_exists Phi s (sigma >>> a) <->
    satisfaction_exists (map (fun phi => pair (fst phi) (snd phi).|[ren sigma]) Phi) s a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    simpl.
    easy.
  -
    split.
    all: simpl.
    all: intros H2.
    all: apply Exists_cons.
    all: apply Exists_cons in H2 as [H2|H2].
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

(** * [satisfaction_conseq] *)

Definition satisfaction_conseq `{S : Signature} :
  relation (list lb_form) :=
  fun Phi Psi =>
  forall `(M : @Model S) (f : nat -> World) (a : assignment),
    satisfaction_forall Phi f a ->
    satisfaction_exists Psi f a.

(** ** Soundness lemmata for [Seq] *)

Lemma satisfaction_conseq_empty `{Signature} :
  forall ls rs phi,
    In (pair nil phi) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1.
  intros M f a H2.
  apply Exists_exists.
  eexists; split; try exact H1.
  apply empty_state_property.
Qed.

Lemma satisfaction_conseq_id `{Signature} :
      forall ls rs ns1 ns2 p args,
        In (pair ns1 (Pred p args)) ls ->
        In (pair ns2 (Pred p args)) rs ->
        In_eq ns1 ns2 ->
        satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  apply Exists_exists.
  eexists.
  split.
  -
    exact H2.
  -
    apply Forall_forall with
      (x := pair ns1 (Pred p args))
      in H4; try exact H1.
    unfold satisfaction in *.
    simpl fst in *.
    simpl snd in *.
    rewrite <- H3.
    exact H4.
Qed.

Lemma satisfaction_conseq_Bot_l `{Signature} :
  forall ls rs n ns x,
    In (pair ns (Bot x)) ls ->
    In n ns ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  apply Forall_forall with
    (x := pair ns (Bot x))
    in H3; try assumption.
  specialize (H3 (f n)).
  apply In_iff_inb_false in H3.
  exfalso.
  apply H3.
  apply in_map.
  exact H2.
Qed.

Lemma satisfaction_conseq_Pred_r `{Signature} :
  forall ls rs ns p args,
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
  intros * H1 H2.
  intros M f a H3.
  destruct (classic (exists psi, psi <> (pair ns (Pred p args)) /\ In psi rs /\ satisfaction f a psi)) as [H4|H4].
  {
    destruct H4 as [psi [_ [H4 H5]]].
    apply Exists_exists.
    exists psi.
    split; assumption.
  }
  apply Exists_exists.
  eexists.
  split; try exact H1.
  intros w H5.
  apply In_iff_inb_true in H5 as H6.
  simpl in H6.
  apply in_map_iff in H6 as [n [H6 H7]].
  subst w.
  specialize (H2 n H7 M f a H3).
  apply Exists_exists in H2 as [psi [H8 H9]].
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
  forall ls rs ns1 ns2 p args,
    In (pair ns1 (Pred p args)) ls ->
    In_sublist ns2 ns1 ->
    satisfaction_conseq ((pair ns2 (Pred p args)) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  apply H3.
  apply Forall_forall.
  intros phi [H5|H5].
  -
    subst phi.
    eapply Forall_forall in H4; try exact H1.
    eapply persistency.
    +
      exact H4.
    +
      apply substate_mapping_state.
      exact H2.
  -
    eapply Forall_forall in H4; eassumption.
Qed.

Lemma satisfaction_conseq_Impl_r `{Signature} :
  forall ls rs ns phi psi,
    In (pair ns <{phi -> psi}>) rs ->
    (forall ns',
      In_sublist ns' ns ->
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
  intros * H1 H2.
  intros M f a H3.
  destruct (
    classic (
      exists chi,
        chi <> (pair ns <{phi -> psi}>) /\
        In chi rs /\
        satisfaction f a chi
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    apply Exists_exists.
    exists chi.
    split; assumption.
  }
  apply Exists_exists.
  eexists; split; try exact H1.

  intros t H5 H6.
  simpl in H5.

  apply substate_mapping_state_iff in H5 as [ns2 [H7 H8]].
  rewrite H7 in *; clear H7.

  specialize (H2 ns2 H8).
  assert (H9 :
    satisfaction_forall ((pair ns2 phi) :: ls) f a
  ).
  {
    apply Forall_forall.
    intros chi [H9|H9].
    -
      subst chi.
      exact H6.
    -
      eapply Forall_forall in H3; eassumption.
  }
  specialize (H2 _ _ _ H9).
  apply Exists_exists in H2 as [chi [[HA|HA] HB]].
  -
    subst chi.
    exact HB.
  -
    assert (HC : chi = pair ns <{phi -> psi}>).
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
  forall ls rs ns1 ns2 phi psi,
    In (pair ns1 <{phi -> psi}>) ls ->
    In_sublist ns2 ns1 ->
    satisfaction_conseq ls ((pair ns2 phi) :: rs) ->
    satisfaction_conseq ((pair ns2 psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3 H4.
  intros M f a H5.
  specialize (H3 _ _ _ H5).
  eapply Forall_forall in H5 as H6; try exact H1.
  apply Exists_exists in H3 as [chi [[H7|H7] H8]].
  +
    subst chi.
    apply H4.
    apply Forall_cons_iff.
    split.
    *
      asimpl in H6.
      apply H6.
      --
         apply substate_mapping_state.
         exact H2.
      --
         exact H8.
    *
      exact H5.
  +
    apply Exists_exists.
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Conj_r `{Signature} :
  forall ls rs ns phi psi,
    In (pair ns <{phi /\ psi}>) rs ->
    satisfaction_conseq ls ((pair ns phi) :: rs) ->
    satisfaction_conseq ls ((pair ns psi) :: rs) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  specialize (H2 _ _ _ H4) as H5.
  apply Exists_exists in H5 as [[ns2 psi1] [[H5|H5] H6]].
  +
    injection H5; intros; subst ns2 psi1; clear H5.
    specialize (H3 _ _ _ H4) as H7.
    apply Exists_exists in H7 as [[ns3 psi2] [[H7|H7] H8]].
    *
      injection H7; intros; subst ns3 psi2; clear H7.
      apply Exists_exists.
      eexists.
      split.
      --
         exact H1.
      --
         split; assumption.
    *
      apply Exists_exists.
      eexists; split; eassumption.
  +
    apply Exists_exists.
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Conj_l `{Signature} :
  forall ls rs ns phi psi,
    In (pair ns <{phi /\ psi}>) ls ->
    satisfaction_conseq
    (
      (pair ns phi) :: (pair ns psi) :: ls
    ) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  eapply Forall_forall in H3 as H4; try exact H1.
  destruct H4 as [H4 H5].
  apply H2.
  apply Forall_forall.
  intros chi [H6|[H6|H6]].
  +
    subst chi.
    exact H4.
  +
    subst chi.
    exact H5.
  +
    eapply Forall_forall in H3; try exact H6.
    exact H3.
Qed.

Lemma satisfaction_conseq_Idisj_r `{Signature} :
  forall ls rs ns phi psi,
    In (pair ns <{phi \\/ psi}>) rs ->
    satisfaction_conseq ls
    (
      (pair ns phi) :: (pair ns psi) :: rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  specialize (H2 _ _ _ H3) as H4.
  apply Exists_exists in H4 as [chi [H4 H5]].
  destruct H4 as [H4|[H4|H4]].
  -
    subst chi.
    apply Exists_exists.
    eexists; split; try exact H1.
    left.
    exact H5.
  -
    subst chi.
    apply Exists_exists.
    eexists; split; try exact H1.
    right.
    exact H5.
  -
    apply Exists_exists.
    eexists; split; eassumption.
Qed.

Lemma satisfaction_conseq_Idisj_l `{Signature} :
  forall ls rs ns phi psi,
    In (pair ns <{phi \\/ psi}>) ls ->
    satisfaction_conseq ((pair ns phi) :: ls) rs ->
    satisfaction_conseq ((pair ns psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  eapply Forall_forall in H4 as H5; try exact H1.
  destruct H5 as [H5|H5].
  -
    apply H2.
    apply Forall_forall.
    intros chi [H6|H6].
    +
      subst chi.
      exact H5.
    +
      eapply Forall_forall in H4; eassumption.
  -
    apply H3.
    apply Forall_forall.
    intros chi [H6|H6].
    +
      subst chi.
      exact H5.
    +
      eapply Forall_forall in H4; eassumption.
Qed.

Lemma satisfaction_conseq_Forall_r `{Signature} :
  forall ls rs ns phi,
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
  intros * H1 H2.
  intros M f a H3.

  destruct (
    classic (
      exists chi,
        chi <> (pair ns <{forall phi}>) /\
        In chi rs /\
        satisfaction f a chi
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    apply Exists_exists.
    exists chi; split; assumption.
  }
  apply Exists_exists.
  eexists; split; try exact H1.
  intros i.
  simpl.

  specialize (H2 M f (i .: a)).
  apply Exists_cons in H2 as [H2|H2].
  -
    exact H2.
  -
    apply Exists_exists in H2 as [psi [H5 H6]].
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
  forall ls rs ns phi t,
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
  intros * H1 H2 H3.
  intros M f a H4.
  eapply Forall_forall in H4 as H5; try exact H1.

  apply H3.
  apply Forall_forall.
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
    eapply Forall_forall in H4; eassumption.
Qed.

Lemma satisfaction_conseq_Iexists_r `{Signature} :
  forall ls rs ns phi t,
    In (pair ns <{iexists phi}>) rs ->
    rigid_term t ->
    satisfaction_conseq ls
    (
      (pair ns phi.|[t/]) ::
      rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  specialize (H3 _ _ _ H4) as H5.
  apply Exists_cons in H5 as [H5|H5].
  -
    apply Exists_exists.
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
  forall ls rs ns phi,
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
  intros * H1 H2.
  intros M f a H3.
  eapply Forall_forall in H3 as H4; try exact H1.
  asimpl in H4.
  destruct H4 as [i H4].
  specialize (H2 M f (i .: a)).
  apply satisfaction_exists_subst_var in H2.
  -
    exact H2.
  -
    apply Forall_cons_iff.
    split.
    +
      exact H4.
    +
      apply satisfaction_forall_subst_var.
      exact H3.
Qed.

Lemma satisfaction_conseq_cut `{Signature} :
  forall ls1 ls2 ls rs1 rs2 rs ns phi,
    In_eq ls (ls1 ++ ls2) ->
    In_eq rs (rs1 ++ rs2) ->
    satisfaction_conseq ls1 ((pair ns phi) :: rs1) ->
    satisfaction_conseq ((pair ns phi) :: ls2) rs2 ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3 H4.
  intros M f a H5.

  rewrite H1 in H5.
  rewrite H2.

  apply Forall_app in H5 as [H5 H6].
  apply Exists_app.

  apply H3 in H5.
  apply Exists_cons in H5 as [H5|H5].
  -
    right.
    apply H4.
    apply Forall_cons_iff.
    split; assumption.
  -
    left.
    exact H5.
Qed.

(** ** Soundness *)

Theorem soundness `{Signature} :
  forall Phi Psi,
    Seq Phi Psi ->
    satisfaction_conseq Phi Psi.
Proof.
  induction 1 as
  [ls1 rs1 phi1 H1 (* Seq_empty *)
  |ls1 rs1 ns1 p args H1 H2 (* Seq_id *)
  |ls1 rs1 n ns1 x H1 H2 (* Seq_Bot_l *)
  |ls1 rs1 ns1 p args H1 H2 IH1 (* Seq_Pred_r *)
  |ls1 rs1 ns1 ns2 p args H1 H2 H3 IH1 (* Seq_Pred_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Impl_r *)
  |ls1 rs1 ns1 ns2 phi1 phi2 H1 H2 H3 IH1 H4 IH2 (* Seq_Impl_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Conj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Conj_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Idisj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Idisj_l *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Forall_r *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Forall_l *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Iexists_r *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Iexists_l *)
  |ls1 ls2 ls3 rs1 rs2 rs3 ns1 phi1 H1 H2 H3 IH1 H4 IH2 (* Seq_cut *)].
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
    satisfaction_conseq_Iexists_l,
    satisfaction_conseq_cut.
Qed.

Print Assumptions soundness.

(** * More derivable rules *)

Proposition Seq_weakening_r `{Signature} :
  forall ls rs1 rs2 ns phi,
    In_eq rs2 ((pair ns phi) :: rs1) ->
    Seq ls rs1 ->
    Seq ls rs2.
Proof.
  intros ls rs1 rs2 ns phi H1 H2.
  generalize dependent phi.
  generalize dependent ns.
  generalize dependent rs2.
  induction H2 as
  [ls1 rs1 phi1 H1 (* Seq_empty *)
  |ls1 rs1 ns1 p args H1 H2 (* Seq_id *)
  |ls1 rs1 n ns1 x H1 H2 (* Seq_Bot_l *)
  |ls1 rs1 ns1 p args H1 H2 IH1 (* Seq_Pred_r *)
  |ls1 rs1 ns1 ns2 p args H1 H2 H3 IH1 (* Seq_Pred_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Impl_r *)
  |ls1 rs1 ns1 ns2 phi1 phi2 H1 H2 H3 IH1 H4 IH2 (* Seq_Impl_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Conj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Conj_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Idisj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Idisj_l *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Forall_r *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Forall_l *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Iexists_r *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Iexists_l *)
  |ls1 ls2 ls3 rs1 rs2 rs3 ns1 phi1 H1 H2 H3 IH1 H4 IH2 (* Seq_cut *)].
  all: intros rs ns phi H5.
  - (* Seq_empty *)
    eapply Seq_empty.
    apply H5.
    right.
    eassumption.
  - (* Seq_id *)
    eapply Seq_id.
    +
      eassumption.
    +
      apply H5; right; eassumption.
    +
      assumption.
  - (* Seq_Bot_l *)
    eapply Seq_Bot_l; eassumption.
  - (* Seq_Pred_r *)
    eapply Seq_Pred_r.
    +
      apply H5; right; eassumption.
    +
      intros n H6.
      eapply IH1.
      *
        exact H6.
      *
        admit.
  - (* Seq_Pred_l *)
    eapply Seq_Pred_l.
    +
      exact H1.
    +
      exact H2.
    +
      eapply IH1.
      exact H5.
  - (* Seq_Impl_r *)
    eapply Seq_Impl_r.
    +
      apply H5; right; eassumption.
    +
      intros ns' H6.
      eapply IH1.
      *
        exact H6.
      *
        admit.
  - (* Seq_Impl_l *)
    eapply Seq_Impl_l; try eassumption.
    +
      eapply IH1.
      admit.
    +
      eapply IH2.
      exact H5.
  - (* Seq_Conj_r *)
    eapply Seq_Conj_r.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
    +
      eapply IH2.
      admit.
  - (* Seq_Conj_l *)
    eapply Seq_Conj_l; try eassumption.
    eapply IH1.
    exact H5.
  - (* Seq_Idisj_r *)
    eapply Seq_Idisj_r.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
  - (* Seq_Idisj_l *)
    eapply Seq_Idisj_l; try eassumption.
    +
      eapply IH1.
      exact H5.
    +
      eapply IH2.
      exact H5.
  - (* Seq_Forall_r *)
    eapply Seq_Forall_r.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
  - (* Seq_Forall_l *)
    eapply Seq_Forall_l; try eassumption.
    eapply IH1.
    exact H5.
  - (* Seq_Iexists_r *)
    eapply Seq_Iexists_r.
    +
      apply H5; right; eassumption.
    +
      exact H2.
    +
      eapply IH1.
      admit.
  - (* Seq_Iexists_l *)
    eapply Seq_Iexists_l; try eassumption.
    eapply IH1.
    admit.
  - (* Seq_cut *)
    eapply Seq_cut with (rs2 := ((pair ns phi) :: rs2)).
    +
      exact H1.
    +
      admit.
    +
      eapply IH1.
      admit.
    +
      eapply IH2.
      reflexivity.
Admitted.

Proposition Seq_weakening_l `{Signature} :
  forall ls1 ls2 rs ns phi,
    In_eq ls2 ((pair ns phi) :: ls1) ->
    Seq ls1 rs ->
    Seq ls2 rs.
Proof.
  intros ls1 ls2 rs ns phi H1 H2.
  generalize dependent phi.
  generalize dependent ns.
  generalize dependent ls2.
  induction H2 as
  [ls1 rs1 phi1 H1 (* Seq_empty *)
  |ls1 rs1 ns1 p args H1 H2 (* Seq_id *)
  |ls1 rs1 n ns1 x H1 H2 (* Seq_Bot_l *)
  |ls1 rs1 ns1 p args H1 H2 IH1 (* Seq_Pred_r *)
  |ls1 rs1 ns1 ns2 p args H1 H2 H3 IH1 (* Seq_Pred_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Impl_r *)
  |ls1 rs1 ns1 ns2 phi1 phi2 H1 H2 H3 IH1 H4 IH2 (* Seq_Impl_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Conj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Conj_l *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 (* Seq_Idisj_r *)
  |ls1 rs1 ns1 phi1 phi2 H1 H2 IH1 H3 IH2 (* Seq_Idisj_l *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Forall_r *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Forall_l *)
  |ls1 rs1 ns1 phi1 t H1 H2 H3 IH1 (* Seq_Iexists_r *)
  |ls1 rs1 ns1 phi1 H1 H2 IH1 (* Seq_Iexists_l *)
  |ls1 ls2 ls3 rs1 rs2 rs3 ns1 phi1 H1 H2 H3 IH1 H4 IH2 (* Seq_cut *)].
  all: intros ls ns phi H5.
  - (* Seq_empty *)
    eapply Seq_empty.
    exact H1.
  - (* Seq_id *)
    eapply Seq_id; try eassumption.
    apply H5; right; eassumption.
  - (* Seq_Bot_l *)
    eapply Seq_Bot_l.
    +
      apply H5; right; eassumption.
    +
      exact H2.
  - (* Seq_Pred_r *)
    eapply Seq_Pred_r; try eassumption.
    intros n H6.
    eapply IH1; eassumption.
  - (* Seq_Pred_l *)
    eapply Seq_Pred_l.
    +
      apply H5; right; eassumption.
    +
      exact H2.
    +
      eapply IH1.
      admit.
  - (* Seq_Impl_r *)
    eapply Seq_Impl_r; try eassumption.
    intros ns' H6.
    eapply IH1.
    +
      exact H6.
    +
      admit.
  - (* Seq_Impl_l *)
    eapply Seq_Impl_l.
    +
      apply H5; right; eassumption.
    +
      exact H2.
    +
      eapply IH1.
      exact H5.
    +
      eapply IH2.
      admit.
  - (* Seq_Conj_r *)
    eapply Seq_Conj_r; try eassumption.
    +
      eapply IH1.
      exact H5.
    +
      eapply IH2.
      exact H5.
  - (* Seq_Conj_l *)
    eapply Seq_Conj_l.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
  - (* Seq_Idisj_r *)
    eapply Seq_Idisj_r; try eassumption.
    eapply IH1.
    exact H5.
  - (* Seq_Idisj_l *)
    eapply Seq_Idisj_l.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
    +
      eapply IH2.
      admit.
  - (* Seq_Forall_r *)
    eapply Seq_Forall_r; try eassumption.
    eapply IH1.
    admit.
  - (* Seq_Forall_l *)
    eapply Seq_Forall_l.
    +
      apply H5; right; eassumption.
    +
      exact H2.
    +
      eapply IH1.
      admit.
  - (* Seq_Iexists_r *)
    eapply Seq_Iexists_r; try eassumption.
    eapply IH1.
    exact H5.
  - (* Seq_Iexists_l *)
    eapply Seq_Iexists_l.
    +
      apply H5; right; eassumption.
    +
      eapply IH1.
      admit.
  - (* Seq_cut *)
    eapply Seq_cut with (ls1 := ((pair ns phi) :: ls1)).
    +
      admit.
    +
      exact H2.
    +
      eapply IH1.
      reflexivity.
    +
      eapply IH2.
      admit.
Admitted.

Proposition Seq_mon `{Signature} :
  forall ls rs ns1 ns2 phi,
    In (pair ns1 phi) ls ->
    In_sublist ns2 ns1 ->
    Seq ((pair ns2 phi) :: ls) rs ->
    Seq ls rs.
Proof.
  intros * H1 H2 H3.
  apply Seq_cut with
    (ls1 := ((pair ns1 phi) :: nil))
    (ls2 := ls)
    (rs1 := nil)
    (rs2 := rs)
    (ns := ns2)
    (phi := phi).
  -
    intros psi.
    split.
    +
      intros H4.
      right.
      exact H4.
    +
      intros [H4|H4].
      *
        subst psi.
        exact H1.
      *
        exact H4.
  -
    reflexivity.
  -
    eapply prop_4_6.
    +
      left; reflexivity.
    +
      left; reflexivity.
    +
      exact H2.
  -
    exact H3.
Qed.

From InqLog.FO Require Import Casari.

Proposition prop_6_4 `{Signature} :
  forall phi ns,
    Seq
    ((pair ns (CasariAnt phi)) :: nil)
    ((pair ns (CasariSuc phi)) :: nil).
Proof.
  intros phi ns.
  induction ns as [ns IH] using (well_founded_ind length_order_wf).
  eapply Seq_Forall_r.
  -
    left; reflexivity.
  -
    eapply Seq_Forall_l with (t := Var 0).
    +
      left; reflexivity.
    +
      exact I.
    +
      eapply Seq_Impl_l.
      *
        left; reflexivity.
      *
        reflexivity.
      *
        eapply Seq_Impl_r.
        --
           left; reflexivity.
        --
           intros ns' H1.
           assert (
            {In_sublist ns ns'} + {~ In_sublist ns ns'}
           ) as [H2|H2].
           {
             admit.
           }
           ++
              eapply prop_4_6.
              **
                 asimpl.
                 left; reflexivity.
              **
                 right.
                 right.
                 left; reflexivity.
              **
                 exact H2.
           ++
              assert (H3 : length_order ns' ns).
              {
                admit.
              }
              apply IH in H3.
              assert (H4 :
                Seq
                ((pair ns (CasariAnt phi)) :: nil)
                ((pair ns' (CasariSuc phi)) :: nil)
              ).
              {
                eapply Seq_mon.
                -
                  left; reflexivity.
                -
                  exact H1.
                -
                  apply Seq_weakening_l with
                    (ls1 := ((pair ns' (CasariAnt phi)) :: nil))
                    (ns := ns)
                    (phi := CasariAnt phi).
                  +
                    apply In_eq_cons_cons.
                  +
                    exact H3.
              }
              asimpl.
              eapply Seq_weakening_l.
              admit.
      *
        eapply Seq_Forall_l with (t := Var 0).
        --
           left; reflexivity.
        --
           exact I.
        --
           eapply prop_4_6.
           ++
              left; reflexivity.
           ++
              left.
              asimpl.
              f_equal.
              admit. (* This is fine *)
           ++
              reflexivity.
Admitted.
