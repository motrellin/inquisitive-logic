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

Instance support_proper `{Model} :
  forall f,
    Proper (state_equiv ==> iff) (support f).
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

  Definition s1 : state. 
  Proof.
    refine
    {|
      state_fun := fun w => 
                    match w with
                    | pq => true
                    | q => true
                    | _ => false
                    end
    |}.
    intros [] [] H1; easy.
  Defined.

  Definition s2 : state. 
  Proof.
    refine
    {|
      state_fun := fun w => 
                    match w with
                    | pq => true
                    | p => true
                    | _ => false
                    end
    |}.
    intros [] [] H1; easy.
  Defined.

  Definition s3 : state. 
  Proof.
    refine
    {|
      state_fun := fun w => 
                    match w with
                    | q => true
                    | e => true
                    | _ => false
                    end
    |}.
    intros [] [] H1; easy.
  Defined.

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

Definition restricted_Model `{Model} (s : state) : Model.
Proof.
  unshelve econstructor.
  -
    exact {w : worlds | s w = true}.
  -
    intros [w1] [w2].
    apply worlds_eq.
    exact w1.
    exact w2.
  -
    intros [w] a.
    apply truth_value.
    exact w.
    exact a.
  -
    split.
    +
      intros []; easy.
    +
      intros [] []; easy.
    +
      intros [w1] [w2] [w3] H1 H2.
      rewrite H1; exact H2.
  -
    intros [w1] [w2].
    apply worlds_deceq.
  -
    simpl.
    intros [w1] [w2].
    apply truth_value_proper.
Defined.

Definition restricted_state `{Model} (s t : state) : @state (restricted_Model s).
Proof.
  unshelve econstructor.
  -
    intros [w].
    apply t.
    exact w.
  -
    intros [w1] [w2] H1.
    simpl in *.
    rewrite H1.
    reflexivity.
Defined.

Section prop_3_3_3.
  
    Context `{M : Model}.
  
    Proposition locality : 
      forall f s,
        support f s <->
        @support _ (restricted_Model s) f (restricted_state s s).
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
        simpl in *.
        firstorder.
      - (* TODO: Implication *)
        admit.
      -
        simpl in *.
        firstorder.
    Admitted.
  
End prop_3_3_3.

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
        support f s.
  Proof.
    induction f as [p| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
    all: intros w.
    -
      rewrite satisfies_atom.
      split.
      +
        intros H1.
        exists (singleton w).
        split.
        *
          apply singleton_true.
          reflexivity.
        *
          intros w' H2.
          rewrite <- singleton_true in H2.
          rewrite <- H2 in *; clear H2 w'.
          exact H1.
      +
        firstorder.
    -
      rewrite satisfies_bot.
      firstorder.
      congruence.
    -
      specialize (IH1 w).
      specialize (IH2 w).
      rewrite satisfies_conj.
      split.
      +
        intros [H1 H3].
        apply IH1 in H1.
        apply IH2 in H3.
        destruct H1 as [s1 [H1 H2]].
        destruct H3 as [s2 [H3 H4]].
        clear IH1 IH2.
        simpl in *.
        unshelve eexists.
        unshelve econstructor.
        *
          exact (fun w => s1 w && s2 w).
        *
          intros w1 w2 H5.
          rewrite H5.
          reflexivity.
        *
          repeat split.
          --
             simpl.
             rewrite H1,H3.
             reflexivity.
          --
             apply persistency with (s := s1).
             ++
                intros w' H5.
                simpl in H5.
                apply andb_prop in H5 as [H5 H6].
                exact H5.
             ++
                exact H2.
          --
             apply persistency with (s := s2).
             ++
                intros w' H5.
                simpl in H5.
                apply andb_prop in H5 as [H5 H6].
                exact H6.
             ++
                exact H4.
      +
        firstorder.
    -
      rewrite satisfies_impl.
      simpl.
      specialize (IH1 w).
      specialize (IH2 w).
      split.
      +
        intros H1.
        exists (singleton w).
        split.
        *
          apply singleton_true.
          reflexivity.
        *
          intros t H2 H3.
          apply substate_singleton in H2 as [H2|H2].
          all: rewrite H2 in *; clear H2 t.
          --
             auto.
          --
             apply empty_support.
      +
        intros [s [H1 H2]] H3.
        apply H2.
        *
          intros w' H4.
          rewrite <- singleton_true in H4.
          rewrite <- H4 in *; clear H4 w'.
          exact H1.
        *
          exact H3.
    -
      rewrite satisfies_idisj.
      specialize (IH1 w).
      specialize (IH2 w).
      simpl.
      split.
      +
        intros [H1|H1].
        *
          apply IH1 in H1 as [s [H1 H2]].
          exists s.
          split.
          --
             exact H1.
          --
             left.
             exact H2.
        *
          apply IH2 in H1 as [s [H1 H2]].
          exists s.
          split.
          --
             exact H1.
          --
             right.
             exact H2.
      +
        intros [s [H1 [H2|H2]]].
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
