From Coq Require Export Bool.
From InqLog.Prop Require Export Formulas.

Inductive lpc :=
  | atom : atoms -> lpc
  | bot : lpc
  | conj : lpc -> lpc -> lpc
  | impl : lpc -> lpc -> lpc.

Definition lpc_support `{Model} : lpc -> state -> Prop :=
  lpc_rect
  (fun f => state -> Prop)
  (fun p s => forall w, s w = true -> truth_value w p = true)
  (fun s => forall w, s w = false)
  (fun f1 r1 f2 r2 s => r1 s /\ r2 s)
  (fun f1 r1 f2 r2 s => forall t, substate t s -> r1 t -> r2 t).

Instance LPC : Formula :=
  {|
    form := lpc;
    support _ := lpc_support
  |}.

Instance support_proper : 
  forall `{Model} f, 
    Proper (state_equiv ==> iff) (support f).
Proof.
  intros M f s1 s2 H1.
  induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2].
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
Qed.
  
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

Section prop_3_1_4.

  Context `{Model}.

  Proposition persistency : persistency_property.
  Proof.
    intro f.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2].
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
  Qed.

  Proposition empty_support : empty_support_property.
  Proof.
    intro f.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2].
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
  Qed.

End prop_3_1_4.

Section prop_3_1_6.

  Context `{Model}.

  Proposition support_neg : 
    forall f s,
      support (neg f) s <->
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
      support (disj f1 f2) s <->
      ~ (
        exists t,
          substate t s /\
          consistent t /\
          support f1 t /\
          support f2 t).
  Proof.
  Admitted.

  Proposition support_iff :
    forall f1 f2 s,
      support (iff f1 f2) s <->
      forall t,
        substate t s ->
        (support f1 t <-> support f2 t).
  Proof.
  Admitted.

End prop_3_1_6.

Section prop_3_1_7.

  Context `{Model}.
  Variable w : worlds.

  Proposition satisfies_atom : 
    forall p,
      satisfies w (atom p) <->
      truth_value w p = true.
  Proof.
    intros p.
    simpl.
    split.
    -
      intros H1.
      apply H1.
      unfold singleton.
      destruct (worlds_deceq w w).
      +
        reflexivity.
      +
        contradiction.
    -
      intros H1 w' H2.
      unfold singleton in H2.
      destruct (worlds_deceq w' w).
      +
        subst w'.
        exact H1.
      +
        discriminate.
  Qed.

  Proposition satisfies_bot : 
    ~ satisfies w bot.
  Proof.
    simpl.
    intros H1.
    specialize (H1 w).
    unfold singleton in H1.
    destruct (worlds_deceq w w).
    -
      discriminate.
    -
      contradiction.
  Qed.

  Proposition satisfies_conj : 
    forall f1 f2,
      satisfies w (conj f1 f2) <->
      satisfies w f1 /\ satisfies w f2.
  Proof.
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

End prop_3_1_7.
