From Coq Require Export Bool.
From InqLog.Prop Require Export LP.

Inductive lpc :=
  | atom : atoms -> lpc
  | bot : lpc
  | conj : lpc -> lpc -> lpc
  | impl : lpc -> lpc -> lpc.

Definition lpc_to_lp : lpc -> lp :=
  lpc_rect
  (fun f => lp)
  (fun p => LP.atom p)
  (LP.bot)
  (fun f1 r1 f2 r2 => LP.conj r1 r2)
  (fun f1 r1 f2 r2 => LP.impl r1 r2).

Coercion lpc_to_lp : lpc >-> lp.

Instance LPC : Formula :=
  {|
    form := lpc;
    support _ := lp_support
  |}.

Instance support_proper `{Model} :
  forall f,
    Proper (state_equiv ==> Logic.iff) (support f).
Proof.
  intro.
  exact LP.support_proper.
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
    exact LP.persistency.
  Qed.

  Proposition empty_support : empty_support_property.
  Proof.
    exact LP.empty_support.
  Qed.

End prop_3_1_4.

Section prop_3_1_6.

  Context `{Model}.

  Proposition support_neg : 
    forall f s,
      support (neg f) s <->
      ruling_out s f.
  Proof.
    exact LP.support_neg.
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
    exact LP.support_disj.
  Qed.

  Proposition support_iff :
    forall f1 f2 s,
      support (iff f1 f2) s <->
      forall t,
        substate t s ->
        (support f1 t <-> support f2 t).
  Proof.
    exact LP.support_iff.
  Qed.

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
    unfold singleton in H1.
    destruct (worlds_deceq w w) as [H2|H2].
    -
      discriminate.
    -
      contradict H2.
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

Section prop_3_1_8.

  Context `{Model}.

  Proposition lpc_truth_conditional : 
    forall f s,
      support f s <->
      forall w,
        s w = true ->
        satisfies w f.
  Proof.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    all: intros s.
    -
      split.
      +
        intros H1 w H2 w' H3.
        apply singleton_true in H3.
        rewrite <- H3 in *; clear H3 w'.
        auto.
      +
        intros H1 w H2.
        specialize (H1 w H2 w).
        apply H1.
        rewrite <- singleton_true.
        reflexivity.
    -
      split.
      +
        intros H1 w H2 w'.
        rewrite <- singleton_false.
        intros H3.
        congruence.
      +
        intros H1 w.
        destruct (s w) eqn:H2.
        *
          specialize (H1 w H2 w).
          rewrite <- singleton_false in H1.
          contradict H1.
          reflexivity.
        *
          reflexivity.
    -
      specialize (IH1 s).
      specialize (IH2 s).
      simpl.
      firstorder.
    -
      transitivity (
        forall t, 
          substate t s -> 
          support f1 t -> 
          support f2 t
      ).
      reflexivity.

      transitivity (
        forall t, 
          substate t s -> 
          (
            forall w, 
              t w = true -> 
              satisfies w f1
          ) -> 
          support f2 t
      ).
      firstorder.

      split.
      +
        intros H1 w H2.
        simpl.
        intros t H3 H4.
        apply substate_singleton in H3 as [H3|H3].
        *
          rewrite H3 in *; clear H3 t.

          apply H1.
          --
             intros w' H5.
             apply singleton_true in H5.
             rewrite <- H5 in *; clear H5 w'.
             exact H2.
          --
             intros w' H5.
             apply singleton_true in H5.
             red.
             rewrite <- H5; clear H5 w'.
             exact H4.
        *
          rewrite H3 in *.
          clear H3 t.
          apply empty_support.
      +
        intros H1 t H2 H3.

        rewrite IH2.
        intros w H4.
        unfold satisfies.
        apply H3 in H4 as H5.
        apply H2 in H4 as H6.
        apply H1 in H6 as H7.
        simpl in H7.
        apply H7.
        *
          reflexivity.
        *
          apply IH1.
          intros w' H8.
          apply singleton_true in H8.
          red.
          rewrite <- H8 in *; clear H8 w'.
          exact H5.
  Qed.
        
End prop_3_1_8.
