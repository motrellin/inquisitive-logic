From Coq Require Export Bool.
From InqLog.Prop Require Export Formulas.

Inductive lpc :=
  | atom : atoms -> lpc
  | bot : lpc
  | conj : lpc -> lpc -> lpc
  | impl : lpc -> lpc -> lpc.

Instance LPC : Formula :=
  {|
    form := lpc;
    support := fun _ =>
      lpc_rect
      (fun f => state -> Prop)
      (fun p s => forall w, s w = true -> truth_value w p = true)
      (fun s => forall w, s w = false)
      (fun f1 r1 f2 r2 s => r1 s /\ r2 s)
      (fun f1 r1 f2 r2 s => forall t, substate t s -> r1 t -> r2 t)
  |}.
  
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
