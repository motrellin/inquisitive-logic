From Coq Require Export Bool.
From InqLog.Prop Require Export Formulas.

Inductive lp :=
  | atom : atoms -> lp
  | bot : lp
  | conj : lp -> lp -> lp
  | impl : lp -> lp -> lp
  | idisj : lp -> lp -> lp.

Definition lp_support `{Model} : lp -> state -> Prop :=
  lp_rect
  (fun f => state -> Prop)
  (fun p s => forall w, s w = true -> truth_value w p = true)
  (fun s => forall w, s w = false)
  (fun f1 r1 f2 r2 s => r1 s /\ r2 s)
  (fun f1 r1 f2 r2 s => forall t, substate t s -> r1 t -> r2 t)
  (fun f1 r1 f2 r2 s => r1 s \/ r2 s).

Instance LP : Formula :=
  {|
    form := lp;
    support _ := lp_support
  |}.

Instance support_proper : 
  forall `{Model} f, 
    Proper (state_equiv ==> iff) (support f).
Proof.
  intros M f s1 s2 H1.
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

Section prop_3_3_1.

  Context `{Model}.

  Proposition persistency : persistency_property.
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

  Proposition empty_support : empty_support_property.
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

  Lemma support_iquest : 
    forall f s,
      support (iquest f) s <-> (support f s \/ ruling_out s f).
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

Module ex_3_2_5.

  Import ex_Model_1.

  Let f1 := idisj (atom 0) (atom 1).
  Let f2 := iquest (atom 0).

  Let s1 : state :=
    fun w =>
    match w with
    | pq => true
    | q => true
    | _ => false
    end.

  Let s2 : state :=
    fun w =>
    match w with
    | pq => true
    | p => true
    | _ => false
    end.

  Let s3 : state :=
    fun w =>
    match w with
    | q => true
    | e => true
    | _ => false
    end.

  Example support_f1_s1 : support f1 s1.
  Proof.
    unfold f1.
    simpl.
    right.
    intros w H1.
    destruct w; easy.
  Qed.

  Example support_f1_s2 : support f1 s2.
  Proof.
    left.
    intros w H1.
    destruct w; easy.
  Qed.

  Example support_f2_s2 : support f2 s2.
  Proof.
    left.
    intros w H1.
    destruct w; easy.
  Qed.

  Example support_f2_s3 : support f2 s3.
  Proof.
    unfold f2.
    rewrite support_iquest.
    right.
    intros [t [H1 [H2 H3]]].
    destruct H2 as [w H2].
    specialize (H1 w H2).
    specialize (H3 w H2).
    destruct w; try easy.
  Qed.

End ex_3_2_5.
