From Coq Require Export Bool.
From InqLog.Prop Require Export Models.

(** * Syntax *)

Inductive form :=
  | atom : atoms -> form
  | bot : form
  | conj : form -> form -> form
  | impl : form -> form -> form
  | idisj : form -> form -> form.

(** ** Derived connectives *)

Definition neg : form -> form :=
  fun f =>
  impl f bot.
Definition top : form :=
  neg bot.
Definition disj : form -> form -> form :=
  fun f1 f2 =>
  neg (conj (neg f1) (neg f2)).
Definition iff : form -> form -> form :=
  fun f1 f2 =>
  conj (impl f1 f2) (impl f2 f1).
Definition iquest : form -> form :=
  fun f =>
  idisj f (neg f).

(** * Support semantics *)

Definition support `{Model} : form -> state -> Prop :=
  form_rect
  (fun f => state -> Prop)
  (fun p s => forall w, s w = true -> truth_value w p = true)
  (fun s => forall w, s w = false)
  (fun f1 r1 f2 r2 s => r1 s /\ r2 s)
  (fun f1 r1 f2 r2 s => forall t, substate t s -> r1 t -> r2 t)
  (fun f1 r1 f2 r2 s => r1 s \/ r2 s).

Notation "s |= f" := (support f s) (at level 70) : state_scope.

Instance support_proper `{Model} :
  forall f,
    Proper (state_eq ==> Logic.iff) (support f).
Proof.
  intros f s1 s2 H1.
  induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
  all: simpl.
  -
    split.
    +
      intros H2 w H3.
      apply H2.
      rewrite H1.
      exact H3.
    +
      intros H2 w H3.
      apply H2.
      rewrite <- H1.
      exact H3.
  -
    split.
    +
      intros H2 w.
      rewrite <- H1.
      apply H2.
    +
      intros H2 w.
      rewrite H1.
      apply H2.
  -
    firstorder.
  -
    split.
    +
      intros H2 t H3 H4.
      apply H2.
      *
        rewrite H1.
        exact H3.
      *
        exact H4.
    +
      intros H2 t H3 H4.
      apply H2.
      *
        rewrite <- H1.
        exact H3.
      *
        exact H4.
  -
    firstorder.
Qed.

(** ** Support for derived connectives *)

Definition ruling_out `{Model} (s : state) (f : form) :=
  ~ (
    exists t,
      substate t s /\
      consistent t /\
      t |= f
      ).

Fact ruling_out_not_support `{Model} :
  forall s f,
    consistent s ->
    ruling_out s f ->
    ~ (s |= f).
Proof.
  intros s f H1 H2 H3.
  apply H2.
  exists s.
  repeat split.
  -
    reflexivity.
  -
    exact H1.
  -
    exact H3.
Qed.

Section prop_3_1_6.

  Context `{Model}.

  Proposition support_neg :
    forall f s,
      s |= (neg f) <->
      ruling_out s f.
  Proof.
    intros f s.
    split.
    -
      intros H1.

      red.
      intros [t [H2 [H3 H4]]].

      red in H3.
      destruct H3 as [w H3].

      simpl in H1.

      specialize (H1 t H2 H4 w).
      rewrite H1 in H3.
      discriminate.
    -
      intros H1.

      simpl.
      intros t H2 H3 w.

      red in H1.
      assert (H4 : ~ consistent t).
      {
        firstorder.
      }
      unfold consistent in H4.
      apply not_true_is_false.
      firstorder.
  Qed.

  Proposition support_disj :
    forall f1 f2 s,
      s |= (disj f1 f2) <->
      ~ (
        exists t,
          substate t s /\
          consistent t /\
          ruling_out t f1 /\
          ruling_out t f2).
  Proof.
    intros f1 f2 s.
    unfold disj.
    rewrite support_neg.
    split.
    -
      intros H1 [t [H2 [[w H3] [H4 H5]]]].

      unfold ruling_out in H1.
      apply H1.
      exists t.
      repeat split.
      +
        exact H2.
      +
        exists w.
        exact H3.
      +
        rewrite support_neg.
        exact H4.
      +
        rewrite support_neg.
        exact H5.
    -
      intros H1.
      red.
      intros [t [H2 [[w H3] [H4 H5]]]].
      rewrite support_neg in H4,H5.
      apply H1.
      exists t.
      repeat split.
      +
        exact H2.
      +
        exists w.
        exact H3.
      +
        exact H4.
      +
        exact H5.
  Qed.

  Proposition support_iff :
    forall f1 f2 s,
      s |= (iff f1 f2) <->
      forall t,
        substate t s ->
        (support f1 t <-> support f2 t).
  Proof.
    firstorder.
  Qed.

  Lemma support_iquest :
    forall f s,
      s |= (iquest f) <-> (s |= f \/ ruling_out s f).
  Proof.
    intros f s.
    unfold iquest.
    remember (neg f) as f'.
    simpl.
    subst f'.
    rewrite support_neg.
    reflexivity.
  Qed.

End prop_3_1_6.

(** ** A small example *)

Module ex_3_2_5.

  Import ex_Model_1.

  Let f1 := idisj (atom 0) (atom 1).
  Let f2 := iquest (atom 0).

  Definition s1 : state.
  Proof.
    refine
    {|
      state_fun := fun w => w true
    |}.
    intros w1 w2; auto.
  Defined.

  Definition s2 : state.
  Proof.
    refine
    {|
      state_fun := fun w => w false
    |}.
    intros w1 w2; auto.
  Defined.

  Definition s3 : state.
  Proof.
    refine
    {|
      state_fun := fun w => negb (w false)
    |}.
    intros w1 w2 H1; f_equal; auto.
  Defined.

  Example support_f1_s1 : s1 |= f1.
  Proof.
    unfold f1.
    simpl.
    right.
    intros w H1.
    destruct w; easy.
  Qed.

  Example support_f1_s2 : s2 |= f1.
  Proof.
    left.
    intros w H1.
    exact H1.
  Qed.

  Example support_f2_s2 : s2 |= f2.
  Proof.
    left.
    intros w H1.
    exact H1.
  Qed.

  Example support_f2_s3 : s3 |= f2.
  Proof.
    unfold f2.
    rewrite support_iquest.
    right.
    intros [t [H1 [H2 H3]]].
    destruct H2 as [w H2].
    specialize (H1 w H2).
    specialize (H3 w H2).
    simpl in *.
    rewrite H3 in H1.
    discriminate.
  Qed.

End ex_3_2_5.

(** ** Properties of [support] *)

Section prop_3_3_1.

  Context `{Model}.

  (** *** Persistency *)

  Proposition persistency :
    forall f t s,
      substate t s ->
      s |= f ->
      t |= f.
  Proof.
    intro f.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    all: unfold substate.
    all: simpl.
    all: intros t s H1 H2.
    -
      auto.
    -
      subst.
      unfold empty_state in H1.
      intros w.
      destruct (t w) eqn:H3.
      +
        apply H1 in H3.
        rewrite H2 in H3.
        discriminate.
      +
        reflexivity.
    -
      firstorder.
    -
      firstorder.
    -
      firstorder.
  Qed.

  (** *** Empty support *)

  Proposition empty_support :
    forall f,
      empty_state |= f.
  Proof.
    intro f.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    all: unfold empty_state in *.
    all: simpl.
    -
      discriminate.
    -
      reflexivity.
    -
      split; assumption.
    -
      intros t H1 H2.
      eapply persistency.
      +
        exact H1.
      +
        exact IH2.
    -
      firstorder.
  Qed.

End prop_3_3_1.

Section prop_3_3_3.

    Context `{M : Model}.

    (** *** Locality *)

    Proposition locality :
      forall f s,
        s |= f <->
        @support (restricted_Model s) f (restricted_state s s).
    Proof.
      induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
      all: intros s.
      -
        simpl.
        split.
        +
          intros H1 [w H2] H3.
          auto.
        +
          intros H1 w H2.
          specialize (H1 (exist _ w H2)).
          auto.
      -
        simpl.
        split.
        +
          intros H1 [w H2].
          auto.
        +
          intros H1 w.
          destruct (s w) eqn:H2.
          *
            specialize (H1 (exist _ w H2)).
            simpl in H1.
            congruence.
          *
            reflexivity.
      -
        (** For some reason, [firstorder] is very slow here... *)
        simpl in *.
        specialize (IH1 s).
        specialize (IH2 s).
        destruct IH1 as [IH11 IH12].
        destruct IH2 as [IH21 IH22].
        split; intros [H1 H2]; split; auto.
      - (* TODO: Implication *)
        admit.
      -
        (** Same here... *)
        simpl in *.
        specialize (IH1 s).
        specialize (IH2 s).
        destruct IH1 as [IH11 IH12].
        destruct IH2 as [IH21 IH22].
        split; intros [|]; [left|right|left|right]; auto.
    Admitted.

End prop_3_3_3.

(** * Satisfaction *)

Definition satisfies `{Model} (w : worlds) : form -> Prop :=
  form_rect
  (fun _ => Prop)
  (fun p => truth_value w p = true)
  False
  (fun f1 r1 f2 r2 => r1 /\ r2)
  (fun f1 r1 f2 r2 => r1 -> r2)
  (fun f1 r1 f2 r2 => r1 \/ r2).

Definition satisfies' `{Model} (w: worlds) : form -> bool :=
  form_rec
  (fun _ => bool)
  (fun p => truth_value w p)
  false
  (fun f1 r1 f2 r2 => r1 && r2)
  (fun f1 r1 f2 r2 => implb r1 r2)
  (fun f1 r1 f2 r2 => r1 || r2).

Section prop_3_3_4.

  Context `{Model}.
  Variable w : worlds.

  Theorem reflect_satisfies :
    forall f,
      reflect (satisfies w f) (satisfies' w f).
  Proof.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    -
      simpl.
      destruct (truth_value w p).
      all: constructor.
      all: congruence.
    -
      constructor.
      easy.
    -
      simpl.
      destruct (satisfies' w f1) eqn:H1, (satisfies' w f2) eqn:H2.
      all: inversion IH1.
      all: inversion IH2.
      all: try (left; easy).
      all: try (right; easy).
    -
      simpl.
      destruct (satisfies' w f1) eqn:H1, (satisfies' w f2) eqn:H2.
      all: inversion IH1.
      all: inversion IH2.
      all: try (left; easy).
      right; firstorder.
    -
      simpl.
      destruct (satisfies' w f1) eqn:H1, (satisfies' w f2) eqn:H2.
      all: inversion IH1.
      all: inversion IH2.
      +
        left; left; assumption.
      +
        left; left; assumption.
      +
        left; right; assumption.
      +
        right.
        intros [H4|H4].
        all: contradiction.
  Qed.

  Corollary satisfies_dec :
    forall f,
      {satisfies w f} + {~ satisfies w f}.
  Proof.
    intros f.
    eapply reflect_dec.
    exact (reflect_satisfies f).
  Qed.

  Theorem satisfies_singleton_support :
    forall f,
      satisfies w f <->
      (singleton w) |= f.
  Proof.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    -
      split.
      +
        intros H1 w' H2.
        apply singleton_true in H2.
        rewrite <- H2 in *; clear H2.
        exact H1.
      +
        intros H1.
        apply H1.
        apply singleton_true.
        reflexivity.
    -
      split; try contradiction.
      simpl.
      intros H1.
      specialize (H1 w).
      apply singleton_false in H1.
      apply H1.
      reflexivity.
    -
      firstorder.
    -
      split.
      +
        intros H1 w' H2 H3.
        apply substate_singleton in H2 as [H2|H2].
        all: rewrite H2 in *; clear H2.
        *
          apply IH2.
          apply H1.
          apply IH1.
          exact H3.
        *
          apply empty_support.
      +
        intros H1 H2.
        apply IH2.
        apply H1.
        *
          reflexivity.
        *
          apply IH1.
          exact H2.
    -
      firstorder.
  Qed.

  Proposition satisfies_neg :
    forall f,
      satisfies w (neg f) <->
      ~ satisfies w f.
  Proof.
    firstorder.
  Qed.

  Proposition satisfies_top :
    satisfies w top <-> True.
  Proof.
    firstorder.
  Qed.

  Proposition satisfies_disj :
    forall f1 f2,
      satisfies w (disj f1 f2) <->
      satisfies w f1 \/ satisfies w f2.
  Proof.
    intros f1 f2.
    destruct (satisfies_dec f1) as [H1|H1], (satisfies_dec f2) as [H2|H2].
    all: firstorder.
  Qed.

  Proposition satisfies_iff :
    forall f1 f2,
      satisfies w (iff f1 f2) <->
      (satisfies w f1 -> satisfies w f2) /\
      (satisfies w f2 -> satisfies w f1).
  Proof.
    firstorder.
  Qed.

End prop_3_3_4.

Corollary reflect_satisfies_eq `{Model} :
  forall w1 w2 f1 f2,
    (satisfies' w1 f1 = satisfies' w2 f2) <->
    (satisfies w1 f1 <-> satisfies w2 f2).
Proof.
  intros w1 w2 f1 f2.
  pose proof (reflect_satisfies w1 f1) as H1.
  pose proof (reflect_satisfies w2 f2) as H2.
  inversion H1; subst; inversion H2; subst; firstorder; easy.
Qed.

Instance satisfies_proper `{Model} : Proper (worlds_eq ==> eq ==> Logic.iff) satisfies.
Proof.
  intros w1 w2 H1 f1 f2 H2.
  do 2 rewrite satisfies_singleton_support.
  rewrite H1, H2.
  reflexivity.
Qed.

Instance satisfies'_proper `{Model} : Proper (worlds_eq ==> eq ==> eq) satisfies'.
Proof.
  intros w1 w2 H1 f1 f2 H2.
  apply reflect_satisfies_eq.
  apply satisfies_proper; assumption.
Qed.

Definition truth_set `{Model} (f : form) : state.
Proof.
  unshelve econstructor.
  -
    intros w.
    apply satisfies'.
    +
      exact w.
    +
      exact f.
  -
    intros w1 w2 H1.
    rewrite H1.
    reflexivity.
Defined.

Section prop_3_3_5.

  Context `{Model}.

  Proposition prop_3_3_5 :
    forall f w,
      satisfies w f <->
      exists (s : state),
        s w = true /\
        s |= f.
  Proof.
    intros f w.
    split.
    -
      intros H1.
      exists (singleton w).
      split.
      +
        apply singleton_true.
        reflexivity.
      +
        rewrite satisfies_singleton_support in H1.
        exact H1.
    -
      induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
      all: intros [s [H1 H2]].
      +
        apply H2.
        exact H1.
      +
        congruence.
      +
        firstorder.
      +
        intros H3.
        apply IH2.
        exists (singleton w).
        split.
        *
          apply singleton_true.
          reflexivity.
        *
          simpl in H2.
          apply H2.
          --
             intros w' H4.
             apply singleton_true in H4.
             rewrite <- H4 in *; clear H4 w'.
             exact H1.
          --
             apply satisfies_singleton_support.
             exact H3.
      +
        firstorder.
  Qed.

End prop_3_3_5.

(** * Truth-Conditionality *)

Definition truth_conditional (f : form) :=
  forall `(M : Model) (s : state),
  s |= f <->
  forall w,
    s w = true ->
    satisfies w f.

Definition statement (f : form) : Prop := truth_conditional f.
Definition question (f : form) : Prop := ~ truth_conditional f.

Definition classical : form -> form :=
  form_rec
  (fun f => form)
  (fun p => atom p)
  bot
  (fun f1 r1 f2 r2 => conj r1 r2)
  (fun f1 r1 f2 r2 => impl r1 r2)
  (fun f1 r1 f2 r2 => disj r1 r2).

Section prop_3_4_3.

  Context `{Model}.

  Proposition classical_truth_set :
    forall f w,
      satisfies w f <->
      satisfies w (classical f).
  Proof.
    intros f w.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    all: simpl classical.
    -
      reflexivity.
    -
      reflexivity.
    -
      firstorder.
    -
      firstorder.
    -
      rewrite satisfies_disj.
      firstorder.
  Qed.

End prop_3_4_3.
