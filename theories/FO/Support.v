From Coq Require Export List FunctionalExtensionality.

From InqLog.FO Require Export Syntax States.

(** * Support satisfaction
   In this section, we will introduce the notion of a state
   _supporting_ a formula (with respect to a variable
   assignment function).

   We refer to a variable assignment function by the short
   name [assignment].
 *)

Definition assignment `{Model} : Type := var -> Individual.

(**
   To interpret a term, we define the [referent] of a term in
   a world which is an [Individual].
 *)

Fixpoint referent `{Model} (t : term) : World -> assignment -> Individual :=
  match t with
  | Var v =>
      fun _ g =>
      g v
  | Func f args =>
      fun w g =>
      FInterpretation w f (fun arg => referent (args arg) w g)
  end.

Lemma rigidity_referent `{Model} :
  forall t w w' a,
    rigid_term t ->
    referent t w a =
    referent t w' a.
Proof.
  induction t as [x|f args IH].
  all: intros w w' a H1.
  -
    reflexivity.
  -
    destruct H1 as [H1 H2].
    simpl.

    erewrite rigidity; try assumption.
    f_equal.
    eauto using functional_extensionality.
Qed.

Lemma referent_subst `{Model} :
  forall t w a sigma,
    (forall x, rigid_term (sigma x)) ->
    referent t.[sigma] w a = referent t w (fun x => referent (sigma x) w a).
Proof.
  induction t as [x|f args IH].
  -
    autosubst.
  -
    intros a w sigma H1.
    asimpl.
    f_equal.
    eauto using functional_extensionality.
Qed.

Remark referent_subst_var `{Model} :
  forall t w a sigma,
    referent t.[ren sigma] w a = referent t w (sigma >>> a).
Proof.
  intros t w a sigma.
  rewrite referent_subst.
  -
    reflexivity.
  -
    easy.
Qed.

Lemma unnamed_helper_Support_24 `{Model} :
  forall w a i sigma,
    (fun x => referent (up sigma x) w (i .: a)) =
    i .: (fun x => referent (sigma x) w a).
Proof.
  intros.
  apply functional_extensionality.
  intros [|x'].
  -
    autosubst.
  -
    asimpl.
    apply referent_subst_var.
Qed.

(**
   Now, we're in a position to define the [support] relation
   as Ciardelli did.
 *)

Fixpoint support `{Model} (phi : form) : state -> assignment -> Prop :=
  match phi with
  | Pred p args =>
      fun s a =>
      forall (w : World),
        s w = true ->
        PInterpretation w p (fun arg => referent (args arg) w a) = true

  | Bot _ =>
      fun s a =>
      forall (w : World),
        s w = false

  | Impl phi1 phi2 =>
      fun s a =>
      forall (t : state),
        substate t s ->
        support phi1 t a ->
        support phi2 t a

  | Conj phi1 phi2 =>
      fun s a =>
      support phi1 s a /\
      support phi2 s a

  | Idisj phi1 phi2 =>
      fun s a =>
      support phi1 s a \/
      support phi2 s a

  | Forall phi1 =>
      fun s a =>
      forall (i : Individual),
        support phi1 s (i .: a)

  | Iexists phi1 =>
      fun s a =>
      exists (i : Individual),
        support phi1 s (i .: a)

  end.

(**
   Again, we introduce some notation.
 *)

Notation "M , s , a |= phi" := (@support _ M phi s a)
    (at level 95)
    : form_scope.

Notation "s , a |= phi" := (support phi s a)
    (at level 95)
    : form_scope.
(* TODO: Why can't I increase the level to anythin higher? *)

(**
   In order to make future proofs more readable, we restate
   the defining cases of [support] as various [Fact]s. They
   can be used for the [rewrite]-tactic.
 *)

Fact support_Pred `{Model} :
  forall p args s a,
    s, a |= <{Pred p args}> <->
    forall w,
      s w = true ->
      PInterpretation w p (fun arg => referent (args arg) w a) = true.
Proof. reflexivity. Qed.

Fact support_Bot `{Model} :
  forall x s a,
    s, a |= <{Bot x}> <->
    forall w,
      s w = false.
Proof. reflexivity. Qed.

Fact support_Impl `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 -> phi2}> <->
    forall t,
      substate t s ->
      t, a |= phi1 ->
      t, a |= phi2.
Proof. reflexivity. Qed.

Fact support_Conj `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 /\ phi2}> <->
    (s, a |= phi1) /\
    (s, a |= phi2).
Proof. reflexivity. Qed.

Fact support_Idisj `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 \\/ phi2}> <->
    (s, a |= phi1) \/
    (s, a |= phi2).
Proof. reflexivity. Qed.

Fact support_Forall `{Model} :
  forall phi1 s a,
  s, a |= <{forall phi1}> <->
    forall i,
      s, i.: a |= phi1.
Proof. reflexivity. Qed.

Fact support_Iexists `{Model} :
  forall phi1 s a,
    s, a |= <{iexists phi1}> <->
    exists i,
      s, i .: a |= phi1.
Proof. reflexivity. Qed.

(**
   Next, we observe, that [state_eq] is a congruence with
   respect to [support].
 *)

Instance support_Proper `{M : Model} :
  forall phi,
    Proper (state_eq ==> eq ==> iff) (support phi).
Proof.
  intros phi s1 s2 H1 a1 a2 H2.
  subst a2.
  generalize dependent a1.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  -
    simpl.
    firstorder.
    all: eauto.
  -
    simpl.
    firstorder.
    all: congruence.
  -
    intros a1.
    do 2 rewrite support_Impl.
    split.
    all: intros H3 s3 H4 H5.
    +
      apply H3.
      *
        rewrite H1.
        exact H4.
      *
        exact H5.
    +
      apply H3.
      *
        rewrite <- H1.
        exact H4.
      *
        exact H5.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
Qed.

(** ** Basic properties *)

Proposition persistency `{Model} :
  forall s t a phi,
  s, a |= phi ->
    substate t s ->
    t, a |= phi.
Proof.
  intros s t a phi.
  revert a.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].

  all: intros a H1 H2.
  -
    firstorder.
  -
    intros w.
    destruct (t w) eqn:H3; try reflexivity.
    specialize (H1 w).
    apply H2 in H3.
    congruence.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    destruct H1 as [i H1].
    exists i.
    eauto.
Qed.

Proposition empty_state_property `{Model} :
  forall (a : assignment) (phi : form),
    empty_state, a |= phi.
Proof.
  intros a phi.
  revert a.

  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros a.
  -
    discriminate.
  -
    rewrite support_Bot.
    reflexivity.
  -
    intros t H1 H2.
    eapply persistency.
    apply substate_empty_state in H1.
    all: auto.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
  -
    firstorder.
    exact Individual_inh.
Qed.

(** ** Ruling out a formula *)

Definition ruling_out `{Model} (s : state) (phi : form) (a : assignment) :=
  ~ exists t,
    consistent t /\
    substate t s /\
    (t, a |= phi).

(* TODO: Rewrite lemmas for [ruling_out] *)

Notation "M , s , a _||_ phi" := (@ruling_out _ M s phi a)
  (at level 95)
  : form_scope.

Notation "s , a _||_ phi" := (ruling_out s phi a)
  (at level 95)
  : form_scope.

(** ** Support conditions for defined connectives *)

Proposition support_Neg `{Model} :
  forall phi s a,
    s, a |= <{~ phi}> <->
    (s, a _||_ phi).
Proof.
  intros phi s a.
  unfold Neg.
  rewrite support_Impl.
  split.
  -
    intros H1 [t [[w H2] [H3 H4]]].
    specialize (H1 t H3 H4).
    rewrite support_Bot in H1.
    congruence.
  -
    intros H1 t H2 H3 w.
    destruct (t w) eqn:H5; try reflexivity.
    exfalso.
    apply H1.
    exists t.
    repeat split.
    all: firstorder.
Qed.

Proposition support_Top `{Model} :
  forall s a,
    s, a |= <{Top}>.
Proof.
  intros s a.
  unfold Top.
  rewrite support_Neg.
  intros [t [[w H1] [H2 H3]]].
  specialize (H3 w).
  congruence.
Qed.

Proposition support_Disj `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 \/ phi2}> <->
    ~ exists t,
      consistent t /\
      substate t s /\
      (t, a _||_ phi1) /\
      (t, a _||_ phi2).
Proof.
  intros phi1 phi2 s a.
  unfold Disj.
  rewrite support_Neg.
  split.
  -
    intros H1.
    intros [t [H2 [H3 [H4 H5]]]].
    apply H1.
    exists t.
    rewrite support_Conj.
    do 2 rewrite support_Neg.
    auto.
  -
    intros H1.
    intros [t [H2 [H3 [H4 H5]]]].
    apply H1.
    exists t.
    rewrite support_Neg in H4,H5.
    auto.
Qed.

Proposition support_Iff `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 <-> phi2}> <->
    forall t,
      substate t s ->
      t,a |= phi1 <->
      (t,a |= phi2).
Proof.
  firstorder.
Qed.

(** ** Support for lifted formulas *)

Lemma support_subst `{Model} :
  forall phi s a sigma w,
    (forall x, rigid_term (sigma x)) ->
    (s, (fun x => referent (sigma x) w a) |= phi) <->
    (s, a |= phi.|[sigma]).
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros s a sigma w H1.
  -
    split.
    all: intros H2 w' H3.
    all: specialize (H2 w' H3).
    all: rewrite <- H2.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros arg.
    +
      etransitivity.
      *
        apply referent_subst.
        exact H1.
      *
        do 2 f_equal.
        apply functional_extensionality.
        intros x.
        apply rigidity_referent.
        exact (H1 x).
    +
      symmetry.
      etransitivity.
      *
        apply referent_subst.
        exact H1.
      *
        do 2 f_equal.
        apply functional_extensionality.
        intros x.
        apply rigidity_referent.
        exact (H1 x).
  -
    reflexivity.
  -
    split.
    all: intros H2 t H3 H4.
    all: eapply IH2; try eassumption.
    all: asimpl in H2.
    all: apply H2; try assumption.
    all: eapply IH1; eassumption.
  -
    split.
    all: intros [H2 H3].
    all: split.
    all: try eapply IH1.
    all: try eapply IH2.
    all: eassumption.
  -
    split.
    all: intros [H2|H2].
    all: try eapply IH1 in H2.
    all: try eapply IH2 in H2.
    all: try assumption.
    all: try (left; eassumption).
    all: try (right; eassumption).
  -
    split.
    all: intros H2 i.
    all: asimpl in H2.
    all: specialize (H2 i).
    +
      eapply IH1.
      *
        apply unnamed_helper_Syntax_3.
        exact H1.
      *
        rewrite unnamed_helper_Support_24.
        exact H2.
    +
      eapply IH1 in H2.
      *
        rewrite <- unnamed_helper_Support_24.
        exact H2.
      *
        apply unnamed_helper_Syntax_3.
        exact H1.
  -
    split.
    all: intros [i H2].
    all: exists i.
    +
      eapply IH1.
      *
        apply unnamed_helper_Syntax_3.
        exact H1.
      *
        rewrite unnamed_helper_Support_24.
        exact H2.
    +
      eapply IH1 in H2.
      *
        rewrite <- unnamed_helper_Support_24.
        exact H2.
      *
        apply unnamed_helper_Syntax_3.
        exact H1.
Qed.

Remark support_subst_var `{Model} :
  forall phi s a sigma,
    (s, (sigma >>> a) |= phi) <->
    (s, a |= phi.|[ren sigma]).
Proof.
  intros phi s a sigma.
  destruct (classic (consistent s)) as [[w H1]|H1].
  -
    pose proof support_subst as H2.
    specialize H2 with
      (phi := phi)
      (s := s)
      (a := a)
      (w := w).
    specialize (H2 (ren sigma)).
    apply H2.
    intros x.
    exact I.
  -
    apply empty_state_not_consistent in H1.
    rewrite H1.
    firstorder using empty_state_property.
Qed.

(** ** Support for multiple formulas *)

Fixpoint support_multiple `{Model} (Phi : list form) :
  state -> assignment -> Prop :=

  match Phi with
  | nil =>
      fun _ _ =>
      True
  | phi :: Phi' =>
      fun s a =>
      (s, a |= phi) /\
      support_multiple Phi' s a
  end.

Remark support_multiple_charac `{Model} :
  forall Phi s a,
    (forall phi, In phi Phi -> s, a |= phi) <->
    support_multiple Phi s a.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a.
  -
    firstorder.
  -
    split.
    +
      intros H1.
      split.
      *
        apply H1.
        left.
        reflexivity.
      *
        apply IH.
        intros phi' H2.
        apply H1.
        right.
        exact H2.
    +
      intros [H1 H2] phi' [H3|H3].
      *
        subst phi'.
        exact H1.
      *
        apply IH.
        --
           exact H2.
        --
           exact H3.
Qed.

Fact support_multiple_support `{Model} :
  forall phi s a,
    support_multiple (phi :: nil) s a <->
    (s, a |= phi).
Proof.
  firstorder.
Qed.

Lemma support_multiple_app `{Model} :
  forall Phi Psi s a,
    support_multiple (Phi ++ Psi) s a <->
    support_multiple Phi s a /\
    support_multiple Psi s a.
Proof.
  induction Phi; firstorder.
Qed.

Lemma support_multiple_lift `{Model} :
  forall Phi s a sigma,
    support_multiple Phi s (sigma >>> a) <->
    support_multiple (map (fun phi => phi.|[ren sigma]) Phi) s a.
Proof.
  induction Phi as [|phi Phi' IH].
  -
    reflexivity.
  -
    intros s a sigma.
    split.
    all: intros [H1 H2].
    +
      split.
      *
        apply support_subst_var in H1.
        exact H1.
      *
        apply IH.
        exact H2.
    +
      split.
      *
        apply support_subst_var.
        exact H1.
      *
        apply IH.
        exact H2.
Qed.

Proposition persistency_support_multiple `{Model} :
  forall s t a Phi,
    support_multiple Phi s a ->
    substate t s ->
    support_multiple Phi t a.
Proof.
  induction Phi; firstorder using persistency.
Qed.

(** * Support consequence *)

Definition support_conseq
  `{S : Signature}
  (cxt : list form)
  (phi : form) :
  Prop :=

  forall `(M : @Model S) s a,
    support_multiple cxt s a ->
    s, a |= phi.

Lemma support_conseq_in `{Signature} :
  forall cxt phi,
    In phi cxt ->
    support_conseq cxt phi.
Proof.
  intros cxt phi H1 M s a H2.
  eapply support_multiple_charac.
  -
    exact H2.
  -
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
    (forall psi, In psi cxt2 -> support_conseq cxt1 psi) ->
    support_conseq cxt2 phi ->
    support_conseq cxt1 phi.
Proof.
  intros cxt1 cxt2 phi H1 H2 M s a H3.
  apply H2.
  apply support_multiple_charac.
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
  exact I.
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
  intros cxt phi psi H1 M s a [_ H3].
  apply H1.
  exact H3.
Qed.

Lemma support_conseq_weakening_1 `{S : Signature} :
  forall cxt1 cxt2 phi,
    support_conseq cxt1 phi ->
    support_conseq (cxt1 ++ cxt2) phi.
Proof.
  intros cxt1 cxt2 phi H1 M s a H2.
  apply support_multiple_app in H2 as [H2 _].
  apply H1.
  exact H2.
Qed.

Lemma support_conseq_weakening_2 `{S : Signature} :
  forall cxt1 cxt2 phi,
    support_conseq cxt2 phi ->
    support_conseq (cxt1 ++ cxt2) phi.
Proof.
  intros cxt1 cxt2 phi H1 M s a H2.
  apply support_multiple_app in H2 as [_ H2].
  apply H1.
  exact H2.
Qed.

Lemma support_conseq_Bot_I `{Signature} :
  forall cxt phi,
    support_conseq cxt phi ->
    support_conseq cxt <{~ phi}> ->
    support_conseq cxt (Bot 0).
Proof.
  intros cxt phi H1 H2 M s a H3 w.
  specialize (H1 _ _ _ H3).
  specialize (H2 _ _ _ H3).
  destruct (s w) eqn:H4; try reflexivity.
  exfalso.
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
  intros w.
  rewrite H1.
  reflexivity.
Qed.

Lemma support_conseq_Impl_I `{S : Signature} :
  forall cxt phi psi,
    support_conseq (phi :: cxt) psi ->
    support_conseq cxt <{phi -> psi}>.
Proof.
  intros cxt phi psi H1 M s a H2.
  intros t H3 H4.
  apply H1.
  split.
  all: eauto using persistency_support_multiple.
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
    split.
    +
      exact H1.
    +
      exact H4.
  -
    apply H3.
    split.
    +
      exact H1.
    +
      exact H4.
Qed.

Lemma support_conseq_Forall_I `{S : Signature} :
  forall cxt phi,
    support_conseq (map (fun psi => psi.|[ren (+1)]) cxt) phi ->
    support_conseq cxt <{forall phi}>.
Proof.
  intros cxt phi H1 M s a H2 i.
  apply H1.
  apply support_multiple_lift.
  exact H2.
Qed.

Lemma support_conseq_Forall_E_rigid `{Signature} :
  forall cxt phi t,
    rigid_term t ->
    support_conseq cxt <{forall phi}> ->
    support_conseq cxt phi.|[t/].
Proof.
  intros cxt phi t H1 H2 M s a H3.
  specialize (H2 _ _ _ H3).
  rewrite support_Forall in H2.
  destruct (classic (consistent s)) as [[w H4]|H4].
  -
    specialize (H2 (referent t w a)).
    apply support_subst with
      (phi := phi)
      (s := s)
      (a := a)
      (sigma := (t .: ids))
      (w := w).
    +
      intros [|x']; easy.
    +
      assert (H5 :
        (fun x => referent ((t .: ids) x) w a) =
        referent t w a .: a
      ).
      {
        apply functional_extensionality.
        intros [|x']; autosubst.
      }
      rewrite H5.
      exact H2.
  -
    apply empty_state_not_consistent in H4.
    rewrite H4.
    apply empty_state_property.
Qed.

Lemma support_conseq_Forall_E_classic `{S : Signature} :
  forall cxt phi t,
    classical phi = true ->
    support_conseq cxt <{forall phi}> ->
    support_conseq cxt phi.|[t .: ids].
Proof.
Admitted.

Lemma support_conseq_Iexists_I `{S : Signature} :
  forall cxt phi t,
    rigid_term t ->
    support_conseq cxt phi.|[t .: ids] ->
    support_conseq cxt <{iexists phi}>.
Proof.
  intros cxt phi t H1 H2 M s a H3.
  specialize (H2 _ _ _ H3).
  destruct (classic (consistent s)) as [[w H4]|H4].
  -
    exists (referent t w a).
    apply support_subst with
      (phi := phi)
      (s := s)
      (a := a)
      (sigma := (t .: ids))
      (w := w)
      in H2.
    +
      assert (H5 :
        (fun x => referent ((t .: ids) x) w a) =
        referent t w a .: a
      ).
      {
        apply functional_extensionality.
        intros [|x']; autosubst.
      }
      rewrite H5 in H2.
      exact H2.
    +
      intros [|x']; easy.
  -
    apply empty_state_not_consistent in H4.
    rewrite H4.
    apply empty_state_property.
Qed.

Lemma support_conseq_Iexists_E `{S : Signature} :
  forall cxt phi psi,
    support_conseq cxt <{iexists phi}> ->
    support_conseq (phi :: map (fun chi => chi.|[ren (+1)]) cxt) psi.|[ren (+1)] ->
    support_conseq cxt psi.
Proof.
  intros cxt phi psi H1 H2 M s a H3.
  specialize (H1 _ _ _ H3) as [i H4].
  enough (H6 : s, i .: a |= psi.|[ren (+1)]).
  {
    apply support_subst_var in H6.
    exact H6.
  }
  apply H2.
  split.
  -
    exact H4.
  -
    apply support_multiple_lift.
    exact H3.
Qed.

Lemma support_conseq_CRAA `{S : Signature} :
  forall cxt phi x,
    classical phi = true ->
    support_conseq (<{~ phi}> :: cxt) (Bot x) ->
    support_conseq cxt phi.
Proof.
Admitted.

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

Lemma support_conseq_CD `{S : Signature} :
  forall cxt phi psi,
    let psi' :=
      psi.|[ren (+1)]
    in
    support_conseq cxt <{forall phi \\/ psi'}> ->
    support_conseq cxt <{(forall phi) \\/ psi}>.
Proof.
Admitted.

Lemma support_conseq_KF `{S : Signature} :
  forall cxt phi,
    support_conseq cxt <{forall ~ ~ phi}> ->
    support_conseq cxt <{~ ~ forall phi}>.
Proof.
Admitted.

(** * Support validity *)

Definition support_valid `{Signature} (phi : form) : Prop :=
  support_conseq nil phi.

Remark support_valid_charac `{S : Signature} :
  forall phi,
    (forall `(M : @Model S) s a, s, a |= phi) <->
    support_valid phi.
Proof.
  firstorder.
Qed.

Definition support_multiple_valid `{S: Signature} (Phi : list form) : Prop :=
  forall `(M : @Model S) s a phi,
    In phi Phi ->
    s, a |= phi.

Lemma support_multiple_valid_nil `{S : Signature} :
  support_multiple_valid nil.
Proof.
  firstorder.
Qed.

Lemma support_multiple_valid_cons `{S : Signature} :
  forall phi Phi',
    support_multiple_valid (phi :: Phi') <->
    support_valid phi /\
    support_multiple_valid Phi'.
Proof.
  intros phi Phi'.
  rewrite <- support_valid_charac.
  split.
  -
    intros H1.
    split.
    +
      intros M s a.
      apply H1.
      left.
      reflexivity.
    +
      intros M s a phi' H2.
      apply H1.
      right.
      exact H2.
  -
    intros [H1 H2].
    intros M s a phi' [H3|H3].
    +
      subst phi'.
      apply H1.
    +
      apply H2.
      exact H3.
Qed.

Remark support_valid_conseq_valid `{Signature} :
  forall Phi psi,
    support_multiple_valid Phi ->
    support_conseq Phi psi ->
    support_valid psi.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros psi H1 H2.
  -
    intros M s a.
    apply H2.
  -
    apply support_multiple_valid_cons in H1 as [H11 H12].
    apply IH.
    +
      exact H12.
    +
      intros M s a H3.
      apply H2.
      split.
      *
        apply H11.
        exact I.
      *
        exact H3.
Qed.

Remark support_valid_Impl_conseq `{S : Signature} :
  forall phi psi,
    support_valid <{phi -> psi}> ->
    support_conseq (phi :: nil) psi.
Proof.
  intros phi psi H1 M s a [H2 _].
  specialize (H1 M s a).
  rewrite support_Impl in H1.
  eapply H1.
  -
    exact I.
  -
    reflexivity.
  -
    exact H2.
Qed.

(**
   By defining [PInterpretation] as a boolean predicate, we
   obtain double negation elimination of atoms.
 *)
Example support_valid_DNE_Pred `{Signature} :
  forall p args,
    support_valid <{DNE (Pred p args)}>.
Proof.
  intros p args M s1 a _ s2 H1 H2 w1 H3.
  rewrite support_Neg in H2.

  destruct (
    PInterpretation w1 p (fun arg : PAri p => referent (args arg) w1 a)
  ) eqn:H4; try reflexivity.

  exfalso.
  apply H2.
  exists (singleton w1).
  repeat split.
  -
    exists w1.
    apply singleton_true.
    reflexivity.
  -
    intros w2 H5.
    apply singleton_true in H5.
    congruence.
  -
    rewrite support_Neg.
    intros [s3 [[w2 H5] [H6 H7]]].
    apply substate_singleton in H6 as [H6|H6].
    all: rewrite H6 in *; clear H6.
    +
      discriminate.
    +
      apply singleton_true in H5.
      subst w2.
      rewrite support_Pred in H7.
      specialize (H7 _ (singleton_refl w1)).
      congruence.
Qed.
