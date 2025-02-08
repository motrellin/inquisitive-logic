From InqLog.FO Require Export Truth.

(* whole section from inqbq_aiml *)

(** * Defining the Sequent Calculus

   For the sequent calculus introduced by Litak/Sano, we
   first the define the notion of _labelled formulas_. A
   labelled formel is a pair consisting of a list of
   natural numbers and a formula.

   We will frequently use the notions of [InS_eq] and
   [InS_sublist], as the original paper uses sets to define
   labels.
 *)

Definition label : Type := list nat.

Definition lb_form `{Signature} : Type := (list nat)*form.

Inductive lb_form_eq `{Signature} : relation lb_form :=
  | lb_form_eq_1 :
      forall ns1 ns2 phi1 phi2,
        InS_eq ns1 ns2 ->
        form_eq phi1 phi2 ->
        lb_form_eq (pair ns1 phi1) (pair ns2 phi2).

Instance lb_form_eq_Equiv `{Signature} :
  Equivalence lb_form_eq.
Proof.
  constructor.
  -
    intros [].
    split; reflexivity.
  -
    inversion 1.
    split; easy.
  -
    inversion 1.
    inversion 1.
    split; etransitivity; eassumption.
Qed.

Program Instance lb_form_Setoid `{Signature} : Setoid lb_form.

Instance lb_form_EqDec `{Signature} : EqDec lb_form_Setoid.
Proof.
  intros [l1 phi1] [l2 phi2].
  destruct (l1 == l2) as [H1|H1].
  -
    destruct (phi1 == phi2) as [H2|H2].
    +
      left.
      split; assumption.
    +
      right.
      inversion 1.
      contradiction.
  -
    right.
    inversion 1.
    contradiction.
Qed.

Instance lb_form_Proper `{Signature} :
  Proper (InS_eq ==> form_eq ==> lb_form_eq) pair.
Proof.
  easy.
Qed.

Instance fst_Proper `{Signature} :
  Proper (lb_form_eq ==> InS_eq) fst.
Proof.
  inversion 1.
  assumption.
Qed.

Instance snd_Proper `{Signature} :
  Proper (lb_form_eq ==> form_eq) snd.
Proof.
  inversion 1.
  assumption.
Qed.

Program Definition lb_form_hsubst `{Signature} (sigma : var -> term) :
  Morph lb_form lb_form :=

  {|
    morph :=
      fun phi =>
      pair (fst phi) (snd phi).|[sigma]
  |}.

Next Obligation.
  inversion 1.
  split.
  -
    assumption.
  -
    simpl in *.
    apply form_hsubst.
    assumption.
Qed.

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
        InS (pair nil phi) rs ->
        Seq ls rs
  (**
     The following rules correspond to the original sequent
     calculus.
   *)
  | Seq_id :
      forall ls rs ns1 ns2 p args,
        InS (pair ns1 (Pred p args)) ls ->
        InS (pair ns2 (Pred p args)) rs ->
        InS_eq ns1 ns2 ->
        Seq ls rs
  | Seq_Bot_l :
      forall ls rs n ns x,
        InS (pair ns (Bot x)) ls ->
        InS n ns ->
        Seq ls rs
  | Seq_Pred_r :
      forall ls rs ns p args,
        InS (pair ns (Pred p args)) rs ->
        (forall n,
          InS n ns ->
          Seq ls ((pair (n :: nil) (Pred p args)) :: rs)
        ) ->
        Seq ls rs
  | Seq_Pred_l :
      forall ls rs ns1 ns2 p args,
        InS (pair ns1 (Pred p args)) ls ->
        InS_sublist ns2 ns1 ->
        Seq ((pair ns2 (Pred p args)) :: ls) rs ->
        Seq ls rs
  | Seq_Impl_r :
      forall ls rs ns phi psi,
        InS (pair ns <{phi -> psi}>) rs ->
        (forall ns',
          InS_sublist ns' ns ->
          Seq ((pair ns' phi) :: ls) ((pair ns' psi) :: rs)
        ) ->
        Seq ls rs
  | Seq_Impl_l :
      forall ls rs ns1 ns2 phi psi,
        InS (pair ns1 <{phi -> psi}>) ls ->
        InS_sublist ns2 ns1 ->
        Seq ls ((pair ns2 phi) :: rs) ->
        Seq ((pair ns2 psi) :: ls) rs ->
        Seq ls rs
  | Seq_Conj_r :
      forall ls rs ns phi psi,
        InS (pair ns <{phi /\ psi}>) rs ->
        Seq ls ((pair ns phi) :: rs) ->
        Seq ls ((pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Conj_l :
      forall ls rs ns phi psi,
        InS (pair ns <{phi /\ psi}>) ls ->
        Seq ((pair ns phi) :: (pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Idisj_r :
      forall ls rs ns phi psi,
        InS (pair ns <{phi \\/ psi}>) rs ->
        Seq ls ((pair ns phi) :: (pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Idisj_l :
      forall ls rs ns phi psi,
        InS (pair ns <{phi \\/ psi}>) ls ->
        Seq ((pair ns phi) :: ls) rs ->
        Seq ((pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Forall_r :
      forall ls rs ns phi,
        InS (pair ns <{forall phi}>) rs ->
        Seq
        (
          map (lb_form_hsubst (ren (+1))) ls
        )
        (
          (pair ns phi) ::
          map (lb_form_hsubst (ren (+1))) rs
        ) ->
        Seq ls rs
  | Seq_Forall_l :
      forall ls rs ns phi t,
        InS (pair ns <{forall phi}>) ls ->
        term_rigid t ->
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
        InS (pair ns <{iexists phi}>) rs ->
        term_rigid t ->
        Seq ls
        (
          (pair ns phi.|[t/]) ::
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_l :
      forall ls rs ns phi,
        InS (pair ns <{iexists phi}>) ls ->
        Seq
        (
          (pair ns phi) ::
          map (lb_form_hsubst (ren (+1))) ls
        )
        (
          map (lb_form_hsubst (ren (+1))) rs
        ) ->
        Seq ls rs
  (**
     InS addition, we add the cut elimination rule to our
     calculus, which is shown to be admissible by Litak/Sano.
   *)
  | Seq_cut :
      forall ls1 ls2 ls rs1 rs2 rs ns phi,
        InS_sublist (ls1 ++ ls2) ls ->
        InS_sublist (rs1 ++ rs2) rs ->
        Seq ls1 ((pair ns phi) :: rs1) ->
        Seq ((pair ns phi) :: ls2) rs2 ->
        Seq ls rs.

(** ** Properties of [Seq] *)

Proposition Seq_weakening `{Signature} :
  forall ls1 ls2,
    InS_sublist ls1 ls2 ->
    forall rs1 rs2,
      InS_sublist rs1 rs2 ->
      Seq ls1 rs1 ->
      Seq ls2 rs2.
Proof with eauto.
  intros ls1 ls2 H1 rs1 rs2 H2 H3.
  generalize dependent rs2.
  generalize dependent ls2.
  induction H3 as
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
  all: intros ls H5 rs H6.
  -
    eapply Seq_empty...
  -
    eapply Seq_id...
  -
    eapply Seq_Bot_l...
  -
    eapply Seq_Pred_r...
    intros.
    eapply IH1...
    rewrite H6.
    reflexivity.
  -
    eapply Seq_Pred_l...
    eapply IH1...
    rewrite H5.
    reflexivity.
  -
    eapply Seq_Impl_r...
    intros.
    eapply IH1...
    all: rewrite H5 + rewrite H6.
    all: reflexivity.
  -
    eapply Seq_Impl_l...
    +
      eapply IH1...
      rewrite H6.
      reflexivity.
    +
      eapply IH2...
      rewrite H5.
      reflexivity.
  -
    eapply Seq_Conj_r...
    +
      eapply IH1...
      rewrite H6.
      reflexivity.
    +
      eapply IH2...
      rewrite H6.
      reflexivity.
  -
    eapply Seq_Conj_l...
    eapply IH1...
    rewrite H5.
    reflexivity.
  -
    eapply Seq_Idisj_r...
    eapply IH1...
    rewrite H6.
    reflexivity.
  -
    eapply Seq_Idisj_l...
    +
      eapply IH1...
      rewrite H5.
      reflexivity.
    +
      eapply IH2...
      rewrite H5.
      reflexivity.
  -
    eapply Seq_Forall_r...
    eapply IH1...
    +
      rewrite H5.
      reflexivity.
    +
      rewrite H6.
      reflexivity.
  -
    eapply Seq_Forall_l...
    eapply IH1...
    rewrite H5.
    reflexivity.
  -
    eapply Seq_Iexists_r...
    eapply IH1...
    rewrite H6.
    reflexivity.
  -
    eapply Seq_Iexists_l...
    eapply IH1...
    +
      rewrite H5.
      reflexivity.
    +
      rewrite H6.
      reflexivity.
  -
    eapply Seq_cut...
    all: etransitivity.
    all: eassumption.
Qed.

Instance Seq_Proper `{Signature} :
  Proper (InS_eq ==> InS_eq ==> iff) Seq.
Proof.
  intros ls1 ls2 [H1 H2] rs1 rs2 [H3 H4].
  split.
  all: intros H5.
  all: eapply Seq_weakening.
  all: eassumption.
Qed.

Proposition prop_4_6 `{Signature} :
  forall ls rs ns1 ns2 phi,
  InS (pair ns1 phi) ls ->
  InS (pair ns2 phi) rs ->
  InS_sublist ns2 ns1 ->
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
      eapply Seq_Forall_l with (t := Var 0)...
      *
        apply InS_map_I with
          (f := lb_form_hsubst (ren (+1)))
          in H1.
        exact H1.
      *
        exact I.
      *
        eapply IH1.
        --
           apply InS_cons_I_hd.
           asimpl.
           reflexivity.
        --
           apply InS_cons_I_hd.
           reflexivity.
        --
           exact H3.
  -
    eapply Seq_Iexists_l.
    +
      exact H1.
    +
      eapply Seq_Iexists_r with (t := Var 0).
      *
        apply InS_map_I with
          (f := lb_form_hsubst (ren (+1)))
          in H2.
        exact H2.
      *
        exact I.
      *
        eapply IH1.
        --
           left; reflexivity.
        --
           apply InS_cons_I_hd.
           asimpl.
           reflexivity.
        --
           exact H3.
Qed.

(** ** Some example derivations *)

Example ex_4_5 `{Signature} :
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

Example ex_4_7 `{Signature} :
  forall ns phi psi,
    Seq
    ((pair ns <{iexists phi}>) :: nil)
    ((pair ns <{iexists ~ psi -> phi}>) :: nil).
Proof with (
  try (right; left; asimpl; reflexivity);
  try (left; asimpl; reflexivity);
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
  try (left; asimpl; reflexivity);
  try (right; left; asimpl; reflexivity);
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

Program Definition satisfaction
  `{Model}
  (f : Morph nat World)
  (a : assignment) :
  Morph lb_form Prop :=
  {|
    morph :=
      fun phi =>
      mapping_state f (fst phi), a |= snd phi
  |}.

Next Obligation.
  intros phi1 phi2 H1.
  rewrite H1.
  reflexivity.
Qed.

Instance satisfaction_Proper `{Model} :
  Proper (Morph_eq ==> eq ==> Morph_eq) satisfaction.
Proof.
  intros f1 f2 H1 a1 a2 H2 phi.
  simpl.
  subst a2.
  rewrite H1.
  reflexivity.
Qed.

Lemma satisfaction_hsubst `{Model} :
  forall phi f a sigma w,
    (forall x, term_rigid (sigma x)) ->
    satisfaction f (fun x => referent (sigma x) w a) phi <->
    satisfaction f a (pair (fst phi) (snd phi).|[sigma]).
Proof.
  intros.
  apply support_hsubst.
  exact H1.
Qed.

Lemma satisfaction_hsubst_var `{Model} :
  forall phi f a sigma,
    satisfaction f (sigma >>> a) phi <->
    satisfaction f a (pair (fst phi) (snd phi).|[ren sigma]).
Proof.
  intros.
  apply support_hsubst_var.
Qed.

(** ** [satisfaction_mult] *)

Definition satisfaction_mult
  `{Model}
  (Phi : list lb_form)
  (f : Morph nat World)
  (a : assignment) :
  Prop :=
  mult (satisfaction f a) Phi.

Arguments satisfaction_mult _ /.

Instance satisfaction_mult_Proper `{Model} :
  Proper (InS_eq ==> Morph_eq ==> eq ==> iff) satisfaction_mult.
Proof.
  intros Phi1 Phi2 H1 f1 f2 H2 a1 a2 H3.
  simpl.
  rewrite H1, H2, H3.
  reflexivity.
Qed.

Lemma satisfaction_mult_hsubst_var `{Model} :
  forall Phi f a sigma,
    satisfaction_mult Phi f (sigma >>> a) <->
    satisfaction_mult (map (lb_form_hsubst (ren sigma)) Phi) f a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    simpl.
    easy.
  -
    split.
    all: intros H2.
    all: simpl in *.
    all: apply mult_cons_E_hd in H2 as H3.
    all: apply mult_cons_E_tl in H2 as H4.
    all: apply mult_cons_I.
    all: apply satisfaction_hsubst_var in H3 + apply IH; assumption.
Qed.

(** ** [satisfaction_some] *)

Definition satisfaction_some
  `{Model}
  (Phi : list lb_form)
  (f : Morph nat World)
  (a : assignment) :
  Prop :=

  some (satisfaction f a) Phi.

Arguments satisfaction_some _ /.

Instance satisfaction_some_Proper `{Model} :
  Proper (InS_eq ==> Morph_eq ==> eq ==> iff) satisfaction_some.
Proof.
  intros Phi1 Phi2 H1 f1 f2 H2 a1 a2 H3.
  simpl.
  subst.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma satisfaction_some_hsubst_var `{Model} :
  forall Phi s a sigma,
    satisfaction_some Phi s (sigma >>> a) <->
    satisfaction_some (map (lb_form_hsubst (ren sigma))  Phi) s a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    simpl.
    split.
    all: intros H1.
    all: contradict H1.
    all: apply some_nil_E.
  -
    split.
    all: simpl.
    all: intros H2.
    all: simpl in *.
    all: apply some_cons_E in H2 as [H2|H2].
    all: apply satisfaction_hsubst_var in H2 + apply IH in H2.
    all: apply some_cons_I_hd + apply some_cons_I_tl; assumption.
Qed.

(** * [satisfaction_conseq] *)

Definition satisfaction_conseq `{S : Signature} :
  relation (list lb_form) :=
  fun Phi Psi =>
  forall `(M : @Model S) (f : Morph nat World) (a : assignment),
    satisfaction_mult Phi f a ->
    satisfaction_some Psi f a.

(** ** Soundness lemmata for [Seq] *)

Lemma satisfaction_conseq_empty `{Signature} :
  forall ls rs phi,
    InS (pair nil phi) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1.
  intros M f a H2.
  eexists; split; try exact H1.
  simpl.
  rewrite mapping_state_nil.
  apply empty_state_property.
Qed.

Lemma satisfaction_conseq_id `{Signature} :
      forall ls rs ns1 ns2 p args,
        InS (pair ns1 (Pred p args)) ls ->
        InS (pair ns2 (Pred p args)) rs ->
        InS_eq ns1 ns2 ->
        satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  eexists; split; try exact H2.
  apply H4.
  rewrite H3 in H1.
  exact H1.
Qed.

Lemma satisfaction_conseq_Bot_l `{Signature} :
  forall ls rs n ns x,
    InS (pair ns (Bot x)) ls ->
    InS n ns ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  apply H3 in H1 as H4.
  specialize (H4 (f n)).
  apply InS_iff_inbS_false in H4.
  contradict H4.
  apply InS_map_I.
  exact H2.
Qed.

Lemma satisfaction_conseq_Pred_r `{Signature} :
  forall ls rs ns p args,
    InS (pair ns (Pred p args)) rs ->
    (forall n,
      InS n ns ->
      satisfaction_conseq ls
      (
        (pair (n :: nil) (Pred p args)) :: rs
      )
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  destruct (
    classic (
      exists psi,
        psi =/= (pair ns (Pred p args)) /\
        InS psi rs /\
        satisfaction f a psi)
  ) as [H4|H4].
  {
    destruct H4 as [psi [_ [H4 H5]]].
    exists psi.
    split; assumption.
  }
  eexists; split; try exact H1.
  intros w H5.
  apply InS_iff_inbS_true in H5 as H6.
  simpl in H6.
  apply InS_map_E in H6 as [n [H6 H7]].
  specialize (H2 n H7 M f a H3).
  apply some_cons_E in H2 as [H2|H2].
  +
    simpl in H2.
    specialize (H2 (f n)).
    unfold "_ ==b _" in H2.
    destruct (f n == f n) as [H8|H8].

    specialize (H2 eq_refl).
    rewrite <- H2.

    assert (H9 : PInterpretation w = PInterpretation (f n))
      by (rewrite H6; reflexivity).
    rewrite H9.
    f_equal.
    apply functional_extensionality.
    intros arg.
    rewrite H6.
    reflexivity.

    exfalso.
    apply H8.
    reflexivity.
  +
    destruct H2 as [psi [H21 H22]].
    assert (HA : psi == pair ns (Pred p args)).
    {
      apply NNPP.
      intros HA.
      apply H4.
      eexists; repeat split; eassumption.
    }
    simpl in H5.
    rewrite HA in H22.
    specialize (H22 (f n)).
    rewrite <- H22.

    assert (HB : PInterpretation w = PInterpretation (f n))
      by (rewrite H6; reflexivity).

    rewrite HB.
    f_equal.
    apply functional_extensionality.
    intros arg.
    rewrite H6.
    reflexivity.

    simpl.
    apply InS_iff_inbS_true.
    apply InS_map_I.
    exact H7.
Qed.

Lemma satisfaction_conseq_Pred_l `{Signature} :
  forall ls rs ns1 ns2 p args,
    InS (pair ns1 (Pred p args)) ls ->
    InS_sublist ns2 ns1 ->
    satisfaction_conseq ((pair ns2 (Pred p args)) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  apply H3.
  intros phi H5.
  apply InS_cons_E in H5 as [H5|H5].
  -
    rewrite H5.
    apply H4 in H1 as H6.
    eapply persistency.
    +
      apply H6.
    +
      simpl.
      rewrite H2.
      reflexivity.
  -
    apply H4.
    exact H5.
Qed.

Lemma satisfaction_conseq_Impl_r `{Signature} :
  forall ls rs ns phi psi, InS (pair ns <{phi -> psi}>) rs ->
    (forall ns',
      InS_sublist ns' ns ->
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
        InS chi rs /\
        satisfaction f a chi
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    exists chi.
    split; assumption.
  }
  eexists; split; try exact H1.

  intros t H5.
  simpl in H5.

  apply substate_mapping_state_iff in H5 as [ns2 [H6 H7]].
  rewrite H6 in *; clear H6.

  rename H7 into H6.
  intros H7.

  specialize (H2 ns2 H6).

  assert (H8 :
    satisfaction_mult ((pair ns2 phi) :: ls) f a
  ).
  {
    intros chi H8.
    apply InS_cons_E in H8 as [H8|H8].
    -
      rewrite H8.
      exact H7.
    -
      apply H3.
      exact H8.
  }
  specialize (H2 _ _ _ H8).
  apply some_cons_E in H2 as [H2|H2].
  -
    exact H2.
  -
    destruct H2 as [chi [H21 H22]].
    assert (H9 : chi = pair ns <{phi -> psi}>).
    {
      apply NNPP.
      intros H9.
      apply H4.
      exists chi.
      easy.
    }
    subst chi.
    asimpl in H22.
    apply H22.
    +
      rewrite H6.
      reflexivity.
    +
      exact H7.
Qed.

Lemma satisfaction_conseq_Impl_l `{Signature} :
  forall ls rs ns1 ns2 phi psi,
    InS (pair ns1 <{phi -> psi}>) ls ->
    InS_sublist ns2 ns1 ->
    satisfaction_conseq ls ((pair ns2 phi) :: rs) ->
    satisfaction_conseq ((pair ns2 psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3 H4.
  intros M f a H5.
  specialize (H3 _ _ _ H5).
  apply some_cons_E in H3 as [H3|H3].
  -
    apply H4.
    apply mult_cons_I.
    +
      apply H5 in H1 as H6.
      simpl in H6.
      apply H6.
      *
        simpl.
        rewrite H2.
        reflexivity.
      *
        exact H3.
    +
      exact H5.
  -
    exact H3.
Qed.

Lemma satisfaction_conseq_Conj_r `{Signature} :
  forall ls rs ns phi psi,
    InS (pair ns <{phi /\ psi}>) rs ->
    satisfaction_conseq ls ((pair ns phi) :: rs) ->
    satisfaction_conseq ls ((pair ns psi) :: rs) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  specialize (H2 _ _ _ H4) as H5.
  specialize (H3 _ _ _ H4) as H6.
  apply some_cons_E in H5 as [H5|H5].
  -
    apply some_cons_E in H6 as [H6|H6].
    +
      eexists; split; try exact H1.
      split; assumption.
    +
      exact H6.
  -
    exact H5.
Qed.

Lemma satisfaction_conseq_Conj_l `{Signature} :
  forall ls rs ns phi psi,
    InS (pair ns <{phi /\ psi}>) ls ->
    satisfaction_conseq
    (
      (pair ns phi) :: (pair ns psi) :: ls
    ) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  apply H3 in H1 as H4.
  destruct H4 as [H4 H5].
  apply H2.
  repeat apply mult_cons_I.
  all: assumption.
Qed.

Lemma satisfaction_conseq_Idisj_r `{Signature} :
  forall ls rs ns phi psi,
    InS (pair ns <{phi \\/ psi}>) rs ->
    satisfaction_conseq ls
    (
      (pair ns phi) :: (pair ns psi) :: rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.
  specialize (H2 _ _ _ H3) as H4.
  repeat apply some_cons_E in H4 as [H4|H4].
  -
    eexists; split; try exact H1.
    left.
    exact H4.
  -
    eexists; split; try exact H1.
    right.
    exact H4.
  -
    exact H4.
Qed.

Lemma satisfaction_conseq_Idisj_l `{Signature} :
  forall ls rs ns phi psi,
    InS (pair ns <{phi \\/ psi}>) ls ->
    satisfaction_conseq ((pair ns phi) :: ls) rs ->
    satisfaction_conseq ((pair ns psi) :: ls) rs ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3.
  intros M f a H4.
  apply H4 in H1 as H5.
  destruct H5 as [H5|H5].
  -
    apply H2.
    apply mult_cons_I; assumption.
  -
    apply H3.
    apply mult_cons_I; assumption.
Qed.

Lemma satisfaction_conseq_Forall_r `{Signature} :
  forall ls rs ns phi,
    InS (pair ns <{forall phi}>) rs ->
    satisfaction_conseq
    (
      map (lb_form_hsubst (ren (+1))) ls
    )
    (
      (pair ns phi) ::
      map (lb_form_hsubst (ren (+1))) rs
    ) ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2.
  intros M f a H3.

  destruct (
    classic (
      exists chi,
        chi <> (pair ns <{forall phi}>) /\
        InS chi rs /\
        satisfaction f a chi
    )
  ) as [H4|H4].
  {
    destruct H4 as [chi [_ [H4 H5]]].
    exists chi; split; assumption.
  }
  eexists; split; try exact H1.
  intros i.
  simpl.

  specialize (H2 M f (i .: a)).
  apply some_cons_E in H2 as [H2|H2].
  -
    exact H2.
  -
    destruct H2 as [psi [H21 H22]].
    apply InS_map_E in H21 as [chi [H211 H212]].
    rewrite <- H211 in H22.
    apply satisfaction_hsubst_var in H22.

    assert (H9 : chi = pair ns (Forall phi)).
    {
      apply NNPP.
      intros H9.
      apply H4; eexists; repeat split; eassumption.
    }
    subst chi.
    apply H22.
  -
    apply satisfaction_mult_hsubst_var.
    exact H3.
Qed.

Lemma satisfaction_conseq_Forall_l `{Signature} :
  forall ls rs ns phi t,
    InS (pair ns <{forall phi}>) ls ->
    term_rigid t ->
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
  apply H4 in H1 as H5.
  apply H3.
  apply mult_cons_I.
  -
    destruct ns as [|n ns'].
    +
      simpl.
      rewrite mapping_state_nil.
      apply empty_state_property.
    +
      asimpl.
      asimpl in H5.
      specialize (H5 (referent t (f n) a)).

      eapply support_hsubst with
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
Qed.

Lemma satisfaction_conseq_Iexists_r `{Signature} :
  forall ls rs ns phi t,
    InS (pair ns <{iexists phi}>) rs ->
    term_rigid t ->
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
  apply some_cons_E in H5 as [H5|H5].
  -
    eexists; split; try exact H1.
    destruct ns as [|n ns'].
    +
      simpl.
      exists Individual_inh.
      rewrite mapping_state_nil.
      apply empty_state_property.
    +
      exists (referent t (f n) a).
      asimpl.
      asimpl in H5.
      eapply support_hsubst with
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
    InS (pair ns <{iexists phi}>) ls ->
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
  apply H3 in H1 as H4.
  asimpl in H4.
  destruct H4 as [i H4].
  specialize (H2 M f (i .: a)).
  apply satisfaction_some_hsubst_var in H2.
  -
    exact H2.
  -
    apply mult_cons_I.
    +
      exact H4.
    +
      apply satisfaction_mult_hsubst_var.
      exact H3.
Qed.

Lemma satisfaction_conseq_cut `{Signature} :
  forall ls1 ls2 ls rs1 rs2 rs ns phi,
    InS_sublist (ls1 ++ ls2) ls ->
    InS_sublist (rs1 ++ rs2) rs ->
    satisfaction_conseq ls1 ((pair ns phi) :: rs1) ->
    satisfaction_conseq ((pair ns phi) :: ls2) rs2 ->
    satisfaction_conseq ls rs.
Proof.
  intros * H1 H2 H3 H4.
  intros M f a H5.

  enough (H6 : satisfaction_some (rs1 ++ rs2) f a).
  {
    apply some_app_E in H6 as [H6|H6].
    all: destruct H6 as [psi [H6 H7]].
    all: exists psi.
    all: split.
    all: try exact H7.
    all: apply H2.
    all: apply InS_app_I_1 + apply InS_app_I_2; exact H6.
  }

  assert (H5' : satisfaction_mult (ls1 ++ ls2) f a).
  {
    apply mult_app_I.
    all: intros psi H6.
    all: eapply H5.
    all: apply H1.
    all: apply InS_app_I_1 + apply InS_app_I_2; exact H6.
  }
  clear H5.
  rename H5' into H5.

  apply mult_app_E_1 in H5 as H6.
  apply mult_app_E_2 in H5 as H7.

  apply H3 in H6.
  apply some_cons_E in H6 as [H6|H6].
  -
    apply some_app_I_2.
    apply H4.
    apply mult_cons_I.
    all: assumption.
  -
    apply some_app_I_1.
    exact H6.
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

Proposition Seq_mon `{Signature} :
  forall ls rs ns1 ns2 phi,
    InS (pair ns1 phi) ls ->
    InS_sublist ns2 ns1 ->
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
    intros psi H4.
    simpl in H4.
    apply InS_cons_E in H4 as [H4|H4].
    +
      rewrite H4.
      exact H1.
    +
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

Proposition Seq_Bot_r `{Signature} :
  forall ls rs ns phi,
    InS (pair ns <{~ phi}>) rs ->
    (forall n,
      InS n ns ->
      Seq ((pair (n :: nil) phi) :: ls) rs
    ) ->
    Seq ls rs.
Proof.
  intros * H1 H2.
  eapply Seq_Impl_r.
  {
    exact H1.
  }
  intros [|n ns'] H3.
  -
    eapply Seq_empty.
    apply InS_cons_I_hd.
    reflexivity.
  -
    assert (H4 : InS n ns).
    {
      apply H3.
      apply InS_cons_I_hd.
      reflexivity.
    }
    specialize (H2 n H4).
    apply Seq_weakening with
      (ls1 := (pair (n :: ns') phi) :: ls)
      (rs1 := rs).
    {
      easy.
    }
    {
      apply InS_sublist_cons_I.
      reflexivity.
    }
    eapply Seq_mon with
      (ns2 := n :: nil).
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    {
      apply cons_InS_sublist_I.
      -
        apply InS_cons_I_hd.
        reflexivity.
      -
        apply nil_InS_sublist_I.
    }
    apply Seq_weakening with
      (ls1 := (pair (n :: nil) phi) :: ls)
      (rs1 := rs).
    {
      apply cons_InS_sublist_I.
      -
        apply InS_cons_I_hd.
        reflexivity.
      -
        apply InS_sublist_cons_I.
        apply InS_sublist_cons_I.
        reflexivity.
    }
    {
      reflexivity.
    }
    exact H2.
Qed.

Module Seq_single_unary_predicate.

  Import Syntax_single_unary_predicate.

  Lemma Seq_id' :
    forall ls rs ns1 ns2 t,
      InS (pair ns1 (Pred' t)) ls ->
      InS (pair ns2 (Pred' t)) rs ->
      InS_eq ns1 ns2 ->
      Seq ls rs.
  Proof.
    eauto using Seq_id.
  Qed.

  Lemma Seq_Pred'_r :
    forall ls rs ns t,
      InS (pair ns (Pred' t)) rs ->
      (forall n,
        InS n ns ->
        Seq ls ((pair (n :: nil) (Pred' t)) :: rs)
      ) ->
      Seq ls rs.
  Proof.
    eauto using Seq_Pred_r.
  Qed.

  Lemma Seq_Pred'_l :
    forall ls rs ns1 ns2 t,
      InS (pair ns1 (Pred' t)) ls ->
      InS_sublist ns2 ns1 ->
      Seq ((pair ns2 (Pred' t)) :: ls) rs ->
      Seq ls rs.
  Proof.
    eauto using Seq_Pred_l.
  Qed.

  Example Seq_card_0 :
    Seq nil ((pair nil (card 0)) :: nil).
  Proof.
    eapply Seq_empty.
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
  Qed.

  Opaque Pred'.

  Example Seq_card_1 :
    forall n1,
      Seq nil ((pair (n1 :: nil) (card 1)) :: nil).
  Proof.
    intros n1.
    simp card.
    eapply Seq_Forall_r.
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    unfold Iquest at 1.
    eapply Seq_Idisj_r.
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    unfold Neg at 1.
    eapply Seq_Impl_r.
    {
      apply InS_cons_I_tl.
      apply InS_cons_I_hd.
      reflexivity.
    }
    intros ns' H1.
    apply InS_sublist_singleton_E in H1 as [H1|H1].
    -
      eapply Seq_id'.
      {
        apply InS_cons_I_hd.
        reflexivity.
      }
      {
        apply InS_cons_I_tl.
        apply InS_cons_I_hd.
        reflexivity.
      }
      {
        exact H1.
      }
    -
      eapply Seq_empty.
      {
        apply InS_cons_I_hd.
        rewrite H1.
        reflexivity.
      }
  Qed.

End Seq_single_unary_predicate.
