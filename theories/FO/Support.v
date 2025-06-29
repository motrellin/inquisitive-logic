From InqLog.FO Require Export States Syntax.

(** * Referent of a term

   To interpret a term, we define the [referent] of a term
   in a world which is an [Individual].
 *)

Fixpoint referent `{Model} (t : term) : World -> assignment -> Individual :=
  match t with
  | Var v =>
      fun _ a =>
      a v
  | Func f args =>
      fun w a =>
      FInterpretation w f
      (fun arg => referent (args arg) w a)
  end.

Instance referent_Proper `{Model} :
  Proper (term_eq ==> equiv ==> ext_eq ==> eq)
  referent.
Proof.
  intros t1.
  induction t1 as [x1|f1 args1 IH].
  all: intros [x2|f2 args2] H1 w1 w2 H2 a1 a2 H3.
  all: try contradiction.
  -
    simpl in *.
    congruence.
  -
    simpl in *.
    destruct (f1 == f2) as [H4|H4]; try contradiction.
    simpl in H4.
    subst f2.
    assert (H5 : FInterpretation w1 = FInterpretation w2).
    {
      rewrite H2.
      reflexivity.
    }
    rewrite H5.
    f_equiv.
    intros arg.
    apply IH.
    +
      apply H1.
    +
      exact H2.
    +
      exact H3.
Qed.

Lemma restricted_referent `{M : Model} :
  forall s t w a,
    @referent _ (restricted_Model s) t w a =
    @referent _ M t (proj1_sig w) a.
Proof.
  intros s.
  induction t as [x|f args IH].
  all: intros w a.
  -
    reflexivity.
  -
    simpl.
    apply FInterpretation_Proper_inner.
    intros arg.
    apply IH.
Qed.

Lemma rigidity_referent `{Model} :
  forall t w w' a,
    term_rigid t ->
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

    rewrite rigidity with (w' := w'); try assumption.
    f_equiv.
    intros arg.
    apply IH.
    apply H2.
Qed.

Print Assumptions rigidity_referent.

Lemma referent_subst `{Model} :
  forall t w a sigma,
    referent t.[sigma] w a =
    referent t w (fun x => referent (sigma x) w a).
Proof.
  induction t as [x|f args IH].
  -
    autosubst.
  -
    intros a w sigma.
    asimpl.
    f_equiv.
    intros arg.
    apply IH.
Qed.

Print Assumptions referent_subst.

Corollary referent_subst_var `{Model} :
  forall t w a sigma,
    referent t.[ren sigma] w a = referent t w (sigma >>> a).
Proof.
  intros t w a sigma.
  rewrite referent_subst.
  reflexivity.
Qed.

Print Assumptions referent_subst.

Lemma unnamed_helper_Support_24 `{Model} :
  forall w a i sigma,
    (fun x => referent (up sigma x) w (i .: a)) ==
    i .: (fun x => referent (sigma x) w a).
Proof.
  intros * x.
  revert w a i sigma.
  induction x as [|x' IH].
  all: intros w a i sigma.
  -
    reflexivity.
  -
    simpl.
    assert (H1 : up sigma (S x') == (sigma x').[ren (+1)])
    by apply rename_subst'.
    rewrite H1.
    apply referent_subst_var.
Qed.

Print Assumptions unnamed_helper_Support_24.

(** * Support satisfaction

   We will now introduce the notion of a state
   _supporting_ a formula (with respect to a variable
   assignment function).
 *)

Fixpoint support `{Model} (phi : form) :
  state -> assignment -> Prop :=

  match phi with
  | Pred p args =>
      fun s a =>
      forall (w : World),
        contains s w ->
        PInterpretation w p
        (fun arg => referent (args arg) w a)

  | Bot _ =>
      fun s a =>
      forall (w : World),
        ~ contains s w

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

(**
   In order to make future proofs more readable, we restate
   the defining cases of [support] as various [Fact]s. They
   can be used for the [rewrite]-tactic.
 *)

Fact support_Pred `{Model} :
  forall p args s a,
    s, a |= <{Pred p args}> <->
    forall w,
      contains s w ->
      PInterpretation w p
      (fun arg => referent (args arg) w a).
Proof.
  reflexivity.
Qed.

Fact support_Bot `{Model} :
  forall x s a,
    s, a |= <{Bot x}> <->
    forall w,
      ~ contains s w.
Proof.
  reflexivity.
Qed.

Fact support_Impl `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 -> phi2}> <->
    forall t,
      substate t s ->
      t, a |= phi1 ->
      t, a |= phi2.
Proof.
  reflexivity.
Qed.

Fact support_Conj `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 /\ phi2}> <->
    (s, a |= phi1) /\
    (s, a |= phi2).
Proof.
  reflexivity.
Qed.

Fact support_Idisj `{Model} :
  forall phi1 phi2 s a,
    s, a |= <{phi1 \\/ phi2}> <->
    (s, a |= phi1) \/
    (s, a |= phi2).
Proof.
  reflexivity.
Qed.

Fact support_Forall `{Model} :
  forall phi1 s a,
  s, a |= <{forall phi1}> <->
    forall i,
      s, i.: a |= phi1.
Proof.
  reflexivity.
Qed.

Fact support_Iexists `{Model} :
  forall phi1 s a,
    s, a |= <{iexists phi1}> <->
    exists i,
      s, i .: a |= phi1.
Proof.
  reflexivity.
Qed.

(** ** Basic properties

   First, we observe that [state_eq] is a congruence with
   respect to [support].
 *)

Instance support_Proper `{M : Model} :
  Proper (form_eq ==> state_eq ==> ext_eq ==> iff)
  support.
Proof with (try contradiction).
  intros phi1.
  induction phi1 as
  [p1 args1
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros psi H1 s1 s2 H2 a1 a2 H3.
  all: destruct psi as
  [p2 args2
  |?
  |psi1 psi2
  |psi1 psi2
  |psi1 psi2
  |psi1
  |psi1]...
  all: simpl in H1.
  -
    destruct (p1 == p2) as [H4|H4]; try contradiction.
    simpl in H4.
    subst p2.
    split.
    all: intros H4 w H5.
    all: rewrite H2 in H5 + rewrite <- H2 in H5.
    all: apply H4 in H5.
    all: simpl in H1.
    all: eapply PInterpretation_Proper_inner.
    all: try exact H5.
    all: intros arg.
    all: f_equiv.
    all: try easy.
  -
    simpl.
    firstorder.
    all: congruence.
  -
    destruct H1 as [H11 H12].
    do 2 rewrite support_Impl.
    split.
    all: intros H4 s3 H5 H6.
    all: eapply IH2.
    all: try eassumption + reflexivity.
    all: try apply H4.
    all: try (rewrite H2 + rewrite <- H2; exact H5).
    all: eapply IH1.
    all: eassumption + reflexivity.
  -
    destruct H1 as [H11 H12].
    split.
    all: intros [H4 H5].
    all: split.
    all: eapply IH1 + eapply IH2; eassumption + reflexivity.
  -
    destruct H1 as [H11 H12].
    split.
    all: intros [H4|H4]; [left|right].
    all: eapply IH1 + eapply IH2; eassumption + reflexivity.
  -
    split.
    all: intros H4 i.
    all: rewrite support_Forall in H4.
    all: specialize (H4 i).
    all: eapply IH1.
    all: try eassumption.
    all: f_equiv.
    all: exact H3.
  -
    split.
    all: intros [i H4].
    all: exists i.
    all: eapply IH1.
    all: try eassumption.
    all: f_equiv.
    all: exact H3.
Qed.

(**
   Therefore, we can see [support] as a morphism.
 *)

Program Definition support_Morph `{Model} (s : state) (a : assignment) : Morph form Prop :=
  {|
    morph phi := s,a |= phi
  |}.

Next Obligation.
  intros phi1 phi2 H1.
  now rewrite H1.
Qed.

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
    intros w H3.
    rewrite H2 in H3.
    eapply H1.
    exact H3.
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

Print Assumptions persistency.

Instance support_Proper_substate `{Model} :
  Proper (form_eq ==> substate --> ext_eq ==> impl) support.
Proof.
  intros phi1 phi2 H1 s1 s2 H2 a1 a2 H3 H4.
  eapply persistency.
  -
    rewrite H1,H3 in H4.
    exact H4.
  -
    exact H2.
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
    intros w H1.
    now apply contains_empty_state_E in H1.
  -
    intros t H1 H2.
    rewrite H1.
    apply IH2.
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

Print Assumptions empty_state_property.

Proposition locality `{M : Model} :
  forall phi s a t,
    substate t s ->
    support phi t a <->
    support phi (@restricted_state _ M s t) a.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros s1 a s2 H1.
  -
    split.
    +
      intros H2 w H3.
      apply andb_true_iff in H3 as [_ H3].
      apply H2 in H3.
      simpl.
      eapply PInterpretation_Proper_inner; try exact H3.
      intros arg.
      apply restricted_referent.
    +
      intros H2 w H3.
      apply H1 in H3 as H4.

      specialize (H2 (exist _ _ H4)).
      eapply PInterpretation_Proper_inner; try apply H2.
      *
        intros arg.
        rewrite restricted_referent.
        reflexivity.
      *
        apply andb_true_iff; split; assumption.
  -
    split.
    +
      intros H2 w H3.
      apply andb_true_iff in H3 as [H3 H4].
      eapply H2.
      exact H4.
    +
      intros H2 w H3.
      apply H1 in H3 as H4.
      apply H2 with (w := exist _ w H4).
      apply andb_true_iff.
      split.
      *
        exact H4.
      *
        exact H3.
  -
    split.
    all: intros H2 s3 H3 H4.
    all: rewrite support_Impl in H2.
    +
      apply unrestricted_substate in H3 as H5.
      rewrite (state_eq_restricted_state_unrestricted_state s1 s3) in *.
      eapply IH2.
      {
        etransitivity; eassumption.
      }
      apply H2; try eassumption.
      eapply IH1; try etransitivity; eassumption.
    +
      eapply IH2.
      {
        etransitivity; eassumption.
      }
      apply H2.
      *
        intros w H5.
        apply andb_true_iff in H5 as [H5 H6].
        apply andb_true_iff.
        split.
        --
           exact H5.
        --
           apply H3.
           exact H6.
      *
        apply IH1.
        {
          etransitivity; eassumption.
        }
        exact H4.
  -
    split.
    all: intros [H2 H3].
    all: split.
    all: eapply IH1 + eapply IH2.
    all: eassumption.
  -
    split.
    all: intros [H2|H2].
    all: eapply IH1 in H2 + eapply IH2 in H2.
    all: try (left + right); eassumption.
  -
    split.
    all: intros H2 i.
    all: rewrite support_Forall in H2.
    +
      eapply IH1; auto.
    +
      eapply IH1; eauto.
  -
    split.
    all: intros [i H2].
    +
      exists i.
      eapply IH1; auto.
    +
      exists i.
      eapply IH1; eauto.
Qed.

Print Assumptions locality.

(** ** Ruling out a formula *)

Definition ruling_out `{Model} (s : state) (phi : form) (a : assignment) :=
  ~ exists t,
    consistent t /\
    substate t s /\
    (t, a |= phi).

Notation "M , s , a _||_ phi" := (@ruling_out _ M s phi a)
  (at level 95)
  : form_scope.

Notation "s , a _||_ phi" := (ruling_out s phi a)
  (at level 95)
  : form_scope.

(** ** Support conditions for defined connectives *)

Lemma support_Neg `{Model} :
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
    intros H1 t H2 H3 w H4.
    apply H1.
    exists t.
    repeat split.
    all: firstorder.
Qed.

Lemma support_Top `{Model} :
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

Lemma support_Disj `{Model} :
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

Lemma support_Iff `{Model} :
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

Lemma support_hsubst `{Model} :
  forall phi s a sigma w,
    (forall x, term_rigid (sigma x)) ->
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
    all: eapply PInterpretation_Proper_inner; try exact H2.
    all: intros arg.
    +
      etransitivity.
      *
        apply referent_subst.
      *
        f_equiv.
        intros x.
        apply rigidity_referent.
        exact (H1 x).
    +
      symmetry.
      etransitivity.
      *
        apply referent_subst.
      *
        f_equiv.
        intros x.
        apply rigidity_referent.
        exact (H1 x).
  -
    reflexivity.
  -
    split.
    all: intros H2 t H3 H4.
    all: eapply IH2; try eassumption.
    all: simpl in H2.
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
    all: simpl in H2.
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

Print Assumptions support_hsubst.

Corollary support_hsubst_var `{Model} :
  forall phi s a sigma,
    (s, (sigma >>> a) |= phi) <->
    (s, a |= phi.|[ren sigma]).
Proof.
  intros phi s a sigma.
  destruct (classic (consistent s)) as [[w H1]|H1].
  -
    pose proof support_hsubst as H2.
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
    apply state_eq_empty_state_iff_not_consistent in H1.
    rewrite H1.
    firstorder using empty_state_property.
Qed.

(** ** Support for multiple formulas *)

Definition support_mult
  `{Model}
  (s : state)
  (a : assignment) :
  list form -> Prop :=

  mult (support_Morph s a).

Lemma support_mult_hsubst_var `{Model} :
  forall Phi s a sigma,
    support_mult s (sigma >>> a) Phi <->
    support_mult s a (map (fun phi => phi.|[ren sigma]) Phi).
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    split.
    all: intro.
    all: apply mult_nil_I.
  -
    split.
    all: intros H1.
    all: apply mult_cons_E_tl in H1 as H2.
    all: apply mult_cons_E_hd in H1.
    +
      simpl.
      apply mult_cons_I.
      *
        apply support_hsubst_var in H1.
        exact H1.
      *
        apply IH.
        exact H2.
    +
      apply mult_cons_I.
      *
        apply support_hsubst_var.
        exact H1.
      *
        apply IH.
        exact H2.
Qed.

Proposition persistency_support_mult `{Model} :
  forall s t a Phi,
    support_mult s a Phi ->
    substate t s ->
    support_mult t a Phi.
Proof.
  induction Phi as [|phi Phi' IH].
  -
    intros H1 H2.
    apply mult_nil_I.
  -
    intros H1 H2.
    apply mult_cons_E_hd in H1 as H3.
    apply mult_cons_E_tl in H1 as H4.
    apply mult_cons_I.
    +
      simpl.
      rewrite H2.
      exact H3.
    +
      eapply IH; eassumption.
Qed.

Print Assumptions persistency_support_mult.

(** ** Support for some formulas *)

Definition support_some
  `{Model}
  (s : state)
  (a : assignment) :
  list form -> Prop :=

  some (support_Morph s a).

Lemma support_some_hsubst_var `{Model} :
  forall Phi s a sigma,
    support_some s (sigma >>> a) Phi <->
    support_some s a (map (fun phi => phi.|[ren sigma]) Phi).
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    split.
    all: intros H1.
    all: now apply some_nil_E in H1.
  -
    split.
    all: simpl.
    all: intros H1.
    all: apply some_cons_E in H1 as [H1|H1].
    +
      apply some_cons_I_hd.
      apply support_hsubst_var in H1.
      exact H1.
    +
      apply some_cons_I_tl.
      apply IH.
      exact H1.
    +
      apply some_cons_I_hd.
      apply support_hsubst_var.
      exact H1.
    +
      apply some_cons_I_tl.
      apply IH.
      exact H1.
Qed.

Proposition persistency_support_some `{Model} :
  forall s t a Phi,
    support_some s a Phi ->
    substate t s ->
    support_some t a Phi.
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros H1 H2.
  -
    now apply some_nil_E in H1.
  -
    apply some_cons_E in H1 as [H1|H1].
    +
      apply some_cons_I_hd.
      simpl.
      rewrite H2.
      exact H1.
    +
      apply some_cons_I_tl.
      apply IH; assumption.
Qed.

Print Assumptions persistency_support_some.

(** * Support validity *)

Definition support_valid `{S : Signature} (phi : form) :=
  forall `(M : @Model S) s a,
    s, a |= phi.
