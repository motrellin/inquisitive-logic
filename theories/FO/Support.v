From Coq Require Export FunctionalExtensionality.

From InqLog.FO Require Export States Syntax.

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

Instance referent_Proper `{Model} :
  Proper (term_eq ==> equiv ==> eq ==> eq) referent.
Proof.
  intros t1 t2 H1 w1 w2 H2 a1 a2 H3.
  subst.
  revert a2.
  generalize dependent w2.
  revert w1.
  generalize dependent t2.
  induction t1 as [x1|f1 args1 IH].
  all: intros [x2|f2 args2] H1 w1 w2 H2 a.
  all: try contradiction.
  -
    simpl in *.
    congruence.
  -
    simpl in *.
    destruct (f1 == f2) as [H3|H3]; try contradiction.
    simpl in H3.
    subst f2.
    assert (H4 : FInterpretation w1 = FInterpretation w2).
    {
      rewrite H2.
      reflexivity.
    }
    rewrite H4.
    f_equal.
    apply functional_extensionality.
    intros arg.
    apply IH.
    +
      apply H1.
    +
      exact H2.
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
    f_equal.
    apply functional_extensionality.
    intros arg.
    apply IH.
Qed.

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
    referent t.[sigma] w a =
    referent t w (fun x => referent (sigma x) w a).
Proof.
  induction t as [x|f args IH].
  -
    autosubst.
  -
    intros a w sigma.
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
  reflexivity.
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
  Proper (form_eq ==> state_eq ==> eq ==> iff) support.
Proof with (try contradiction).
  intros phi1 phi2 H1 s1 s2 H2 a1 a2 H3.
  subst a2.
  generalize dependent a1.
  generalize dependent s2.
  revert s1.
  generalize dependent phi2.
  induction phi1 as
  [p1 args1
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros psi H1 s1 s2 H2 a.
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
    destruct (p1 == p2) as [H3|H3]; try contradiction.
    simpl in H3.
    subst p2.
    split.
    all: intros H3 w H4.
    all: rewrite H2 in H4 + rewrite <- H2 in H4.
    all: apply H3 in H4.
    all: red in H1.
    all: rewrite <- H4.
    all: f_equal.
    all: apply functional_extensionality.
    all: intros arg.
    all: rewrite H1.
    all: reflexivity.
  -
    simpl.
    firstorder.
    all: congruence.
  -
    destruct H1 as [H11 H12].
    do 2 rewrite support_Impl.
    split.
    all: intros H3 s3 H4 H5.
    +
      eapply IH2; try eassumption + reflexivity.
      apply H3.
      *
        rewrite H2.
        exact H4.
      *
        eapply IH1; eassumption + reflexivity.
    +
      eapply IH2; try eassumption + reflexivity.
      apply H3.
      *
        rewrite <- H2.
        exact H4.
      *
        eapply IH1; eassumption + reflexivity.
  -
    destruct H1 as [H11 H12].
    split.
    all: intros [H3 H4].
    all: split.
    all: eapply IH1 + eapply IH2; eassumption + reflexivity.
  -
    destruct H1 as [H11 H12].
    split.
    all: intros [H3|H3].
    all: left + right; eapply IH1 + eapply IH2; eassumption + reflexivity.
  -
    split.
    all: intros H3 i.
    all: rewrite support_Forall in H3.
    all: specialize (H3 i).
    all: eapply IH1; eassumption.
  -
    split.
    all: intros [i H3].
    all: exists i.
    all: eapply IH1; eassumption.
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
      rewrite <- H3.
      f_equal.
      apply functional_extensionality.
      intros arg.
      apply restricted_referent.
    +
      intros H2 w H3.
      apply H1 in H3 as H4.

      specialize (H2 (exist _ _ H4)).
      rewrite <- H2.
      simpl.
      f_equal.
      apply functional_extensionality.
      intros arg.
      rewrite restricted_referent.
      reflexivity.

      simpl.
      apply andb_true_iff; split; assumption.
  -
    split.
    +
      intros H2 w.
      apply andb_false_iff.
      right.
      rewrite H2.
      reflexivity.
    +
      intros H2 w.
      destruct (s2 w) eqn:H3; try reflexivity.
      simpl in H2.
      apply H1 in H3 as H4.
      specialize (H2 (exist _ _ H4)).
      apply andb_false_iff in H2 as [H2|H2].
      all: simpl in H2.
      all: congruence.
  -
    split.
    all: intros H2 s3 H3 H4.
    all: rewrite support_Impl in H2.
    +
      apply unrestricted_substate in H3 as H5.
      rewrite (unnamed_States_helper_3 s1 s3) in *.
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

Lemma support_hsubst `{Model} :
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

Remark support_hsubst_var `{Model} :
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
    apply empty_state_not_consistent in H1.
    rewrite H1.
    firstorder using empty_state_property.
Qed.

(** ** Support for multiple formulas *)

Definition support_mult
  `{Model}
  (s : state)
  (a : assignment) :
  list form -> Prop :=

  List.Forall (fun phi => s,a |= phi).

Fact support_mult_support `{Model} :
  forall phi s a,
    support_mult s a (phi :: nil) <->
    (s, a |= phi).
Proof.
  intros phi s a.
  split.
  -
    intros H1.
    eapply Forall_forall in H1.
    +
      exact H1.
    +
      left; reflexivity.
  -
    intros H1.
    repeat constructor + assumption.
Qed.

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
    all: constructor.
  -
    split.
    all: intros H1.
    all: apply Forall_cons_iff in H1 as [H1 H2].
    +
      constructor.
      *
        apply support_hsubst_var in H1.
        exact H1.
      *
        apply IH.
        exact H2.
    +
      constructor.
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
    intros; constructor.
  -
    intros H1 H3.
    apply Forall_cons_iff in H1 as [H1 H2].
    constructor.
    +
      eapply persistency; eassumption.
    +
      eapply IH; eassumption.
Qed.

(** ** Support for some formulas *)

Definition support_some
  `{Model}
  (s : state)
  (a : assignment) :
  list form -> Prop :=

  List.Exists (fun phi => s,a |= phi).

Fact support_some_support `{Model} :
  forall phi s a,
    support_some s a (phi :: nil) <->
    (s, a |= phi).
Proof.
  split.
  all: intros H1.
  -
    apply Exists_cons in H1 as [H1|H1]; easy.
  -
    constructor.
    exact H1.
Qed.

Lemma support_some_hsubst_var `{Model} :
  forall Phi s a sigma,
    support_some s (sigma >>> a) Phi <->
    support_some s a (map (fun phi => phi.|[ren sigma]) Phi).
Proof.
  induction Phi as [|phi Phi' IH].
  all: intros s a sigma.
  -
    split.
    all: inversion 1.
  -
    split.
    all: simpl.
    all: intros H1.
    all: apply Exists_cons.
    all: apply Exists_cons in H1 as [H1|H1].
    +
      left.
      apply support_hsubst_var in H1.
      exact H1.
    +
      right.
      apply IH.
      exact H1.
    +
      left.
      apply support_hsubst_var.
      exact H1.
    +
      right.
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
    inversion H1.
  -
    apply Exists_cons in H1 as [H1|H1].
    +
      left.
      eapply persistency; eassumption.
    +
      right.
      apply IH; assumption.
Qed.

(** * Support validity *)

Definition support_valid `{S : Signature} (phi : form) :=
  forall `(M : @Model S) s a,
    s, a |= phi.

Definition support_valid_mult `{Signature} :
  list form -> Prop :=

  List.Forall support_valid.

Remark support_valid_mult_charac `{S : Signature} :
  forall Phi,
    (forall `(M : @Model S) s a, support_mult s a Phi) <->
    support_valid_mult Phi.
Proof.
  intros Phi.
  split.
  -
    intros H1.
    apply Forall_forall.
    intros phi H2 M s a.
    eapply Forall_forall in H1; eassumption.
  -
    intros H1 M s a.
    apply Forall_forall.
    intros phi H2.
    eapply Forall_forall in H1.
    +
      apply H1.
    +
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
  intros p args M s1 a s2 H1 H2 w1 H3.
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
    rewrite H5.
    exact H3.
  -
    rewrite support_Neg.
    intros [s3 [[w2 H5] [H6 H7]]].
    apply substate_singleton in H6 as [H6|H6].
    all: rewrite H6 in *; clear H6.
    +
      discriminate.
    +
      apply singleton_true in H5.
      rewrite support_Pred in H7.
      specialize (H7 _ (singleton_refl w1)).
      congruence.
Qed.
