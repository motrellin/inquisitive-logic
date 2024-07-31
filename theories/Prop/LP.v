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

Definition satisfies `{Model} (w : worlds) (f : form) :=
  (singleton w) |= f.

Section prop_3_1_7.

  Context `{Model}.
  Variable w : worlds.

  Proposition satisfies_atom :
    forall p,
      satisfies w (atom p) <->
      truth_value w p = true.
  Proof.
    intros p.
    unfold satisfies.
    split.
    -
      intros H1.
      apply H1.
      apply singleton_true.
      reflexivity.
    -
      intros H1 w' H2.
      apply singleton_true in H2.
      rewrite <- H2.
      exact H1.
  Qed.

  Proposition satisfies_bot :
    satisfies w bot <-> False.
  Proof.
    split; try contradiction.
    simpl.
    intros H1.
    specialize (H1 w).
    apply singleton_false in H1.
    apply H1.
    reflexivity.
  Qed.

  Proposition satisfies_conj :
    forall f1 f2,
      satisfies w (conj f1 f2) <->
      satisfies w f1 /\ satisfies w f2.
  Proof.
    simpl in *.
    firstorder.
  Qed.

  Proposition satisfies_impl :
    forall f1 f2,
    satisfies w (impl f1 f2) <->
    (satisfies w f1 -> satisfies w f2).
  Proof.
    intros f1 f2.
    unfold satisfies at 1.
    transitivity (
      forall t, substate t (singleton w) -> support f1 t -> support f2 t
    ).
    -
      simpl.
      firstorder.
    -
      split.
      +
        unfold satisfies.
        intros H1 H2.
        apply H1.
        *
          reflexivity.
        *
          exact H2.
      +
        intros H1 s H2 H3.
        apply substate_singleton in H2.
        unfold satisfies in H1.
        destruct H2 as [H2|H2].
        *
          rewrite H2.
          apply H1.
          rewrite <- H2.
          exact H3.
        *
          rewrite H2.
          apply empty_support.
  Qed.

  Proposition satisfies_neg :
    forall f,
      satisfies w (neg f) <->
      ~ satisfies w f.
  Proof.
    intros f.
    unfold neg.
    rewrite satisfies_impl.
    pose proof satisfies_bot.
    firstorder.
  Qed.

  Proposition satisfies_top :
    satisfies w top <-> True.
  Proof.
    simpl.
    firstorder.
  Qed.

  Proposition satisfies_disj :
    forall f1 f2,
      satisfies w (disj f1 f2) <->
      satisfies w f1 \/ satisfies w f2.
  Proof.
    intros f1 f2.
    unfold disj.
    rewrite satisfies_neg.
    rewrite satisfies_conj.
    rewrite satisfies_neg.
    rewrite satisfies_neg.
    firstorder. (* Missing: classical reasoning *)
  Abort.

  Proposition satisfies_iff :
    forall f1 f2,
      satisfies w (iff f1 f2) <->
      (satisfies w f1 -> satisfies w f2) /\
      (satisfies w f2 -> satisfies w f1).
  Proof.
    intros f1 f2.
    unfold iff.
    rewrite satisfies_conj.
    rewrite satisfies_impl.
    rewrite satisfies_impl.
    reflexivity.
  Qed.

End prop_3_1_7.

Section prop_3_3_4.

  Context `{Model}.

  Proposition satisfies_idisj :
    forall f1 f2 w,
      satisfies w (idisj f1 f2) <->
      satisfies w f1 \/ satisfies w f2.
  Proof.
    firstorder.
  Qed.

End prop_3_3_4.

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
        exact H1.
    -
      induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
      all: intros [s [H1 H2]].
      +
        rewrite satisfies_atom.
        auto.
      +
        congruence.
      +
        rewrite satisfies_conj.
        firstorder.
      +
        rewrite satisfies_impl.
        intros H3.
        apply H2.
        *
          intros w' H4.
          rewrite <- singleton_true in H4.
          rewrite <- H4 in *; clear H4 w'.
          exact H1.
        *
          exact H3.
      +
        rewrite satisfies_idisj.
        destruct H2 as [H2|H2].
        *
          left.
          apply persistency with (s := s).
          intros w' H3.
          apply singleton_true in H3.
          --
             rewrite <- H3 in *; clear H3 w'.
             exact H1.
          --
             exact H2.
        *
          right.
          apply persistency with (s := s).
          intros w' H3.
          apply singleton_true in H3.
          --
             rewrite <- H3 in *; clear H3 w'.
             exact H1.
          --
             exact H2.
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
      do 2 rewrite satisfies_conj.
      firstorder.
    -
      do 2 rewrite satisfies_impl.
      firstorder.
    -
      rewrite satisfies_idisj.
      Fail rewrite satisfies_disj.
  Abort.

End prop_3_4_3.
