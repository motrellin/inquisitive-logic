From Coq Require Export RelationClasses Morphisms Setoid.

Definition atoms := nat.

Class Model :=
  {
    worlds : Type;
    worlds_eq : worlds -> worlds -> Prop;
    worlds_eq_equiv :: Equivalence worlds_eq;
    worlds_deceq : forall (w1 w2 : worlds), {worlds_eq w1 w2} + {~ worlds_eq w1 w2};
    truth_value : worlds -> atoms -> bool;
    truth_value_proper :: Proper (worlds_eq ==> eq ==> eq) truth_value
  }.

Record state `{Model} :=
  {
    state_fun : worlds -> bool;
    state_proper :: Proper (worlds_eq ==> eq) state_fun
  }.

Coercion state_fun : state >-> Funclass.

Definition state_equiv `{Model} (s1 s2 : state) : Prop :=
  forall w, s1 w = s2 w.

Instance state_equiv_equiv : forall `{Model}, Equivalence state_equiv.
Proof.
  split.
  -
    intros s w; reflexivity.
  -
    intros s t H1 w.
    symmetry.
    exact (H1 w).
  -
    intros s t u H1 H2 w.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Definition substate `{Model} (t s : state) :=
  forall w,
    t w = true ->
    s w = true.

#[export] Instance substate_proper :
  forall `{Model},
    Proper (state_equiv ==> state_equiv ==> iff) substate.
Proof.
  intros M s1 s2 H1 t1 t2 H2.
  unfold state_equiv, substate in *.
  split.
  -
    intros H3 w H4.
    rewrite <- H2.
    apply H3.
    rewrite H1.
    exact H4.
  -
    intros H3 w H4.
    rewrite H2.
    apply H3.
    rewrite <- H1.
    exact H4.
Qed.


Instance substate_refl : forall `{Model}, Reflexive substate.
Proof.
  intros M s w H1.
  assumption.
Qed.

Definition empty_state `{Model} : state :=
  {|
    state_fun := fun _ => false;
    state_proper := fun _ _ _ => eq_refl
 |}.

Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    s w = true.

Program Definition singleton `{Model} (w : worlds) : state :=
  {|
    state_fun w' := if worlds_deceq w' w then true else false
 |}.
Obligation 1.
  intros w1 w2 H1.
  destruct (worlds_deceq w1 w) as [H2|H2], (worlds_deceq w2 w) as [H3|H3].
  -
    reflexivity.
  -
    contradict H3.
    rewrite <- H1, <- H2.
    reflexivity.
  -
    contradict H2.
    rewrite H1, <- H3.
    reflexivity.
  -
    reflexivity.
Defined.

Instance singleton_proper :
  forall `{Model},
    Proper (worlds_eq ==> state_equiv) singleton.
Proof.
  intros M w1 w2 H1 w'.
  simpl.
  destruct (worlds_deceq w' w1) as [H2|H2], (worlds_deceq w' w2) as [H3|H3].
  reflexivity.
  contradict H3; rewrite H2; rewrite H1; reflexivity.
  contradict H2; rewrite H1; rewrite H3; reflexivity.
  reflexivity.
Qed.

Lemma substate_singleton `{Model} :
  forall s w,
    substate s (singleton w) ->
    state_equiv s (singleton w) \/
    state_equiv s empty_state.
Proof.
  intros s w H1.
  destruct (s w) eqn:H2.
  -
    left.
    intros w'.
    unfold substate in H1.
    unfold singleton in *.
    destruct (s w') eqn:H3.
    +
      specialize (H1 w').
      simpl in *.
      destruct (worlds_deceq w' w).
      *
        reflexivity.
      *
        symmetry.
        auto.
    +
      simpl in *.
      destruct (worlds_deceq w' w) as [H4|H4].
      *
        rewrite H4 in *; clear H4.
        congruence.
      *
        reflexivity.
  -
    right.
    intros w'.
    unfold substate, singleton in H1.
    destruct (s w') eqn:H3.
    +
      specialize (H1 w' H3).
      simpl in H1.
      destruct (worlds_deceq w' w) as [H4|H4].
      *
        rewrite H4 in *; clear H4.
        congruence.
      *
        discriminate.
    +
      reflexivity.
Qed.

Lemma singleton_true `{Model} :
  forall w w',
    worlds_eq w w' <->
    singleton w w' = true.
Proof.
  intros w w'.
  unfold singleton.
  simpl.
  destruct (worlds_deceq w' w) as [H1|H1].
  -
    rewrite H1 in *; clear H1.
    split.
    +
      intros H1.
      reflexivity.
    +
      intros H1.
      reflexivity.
  -
    split.
    +
      intros H2.
      subst.
      symmetry in H2.
      contradiction.
    +
      intros H2.
      discriminate.
Qed.

Lemma singleton_false `{Model} :
  forall w w',
    (~ worlds_eq w w')  <->
    singleton w w' = false.
Proof.
  intros w w'.
  split.
  -
    intros H1.
    unfold singleton.
    simpl in *.
    destruct (worlds_deceq w' w) as [H2|H2].
    +
      rewrite H2 in *; clear H2.
      contradict H1.
      reflexivity.
    +
      reflexivity.
  -
    intros H1 H2.
    rewrite <- H2 in *; clear H2.
    unfold singleton in H1.
    simpl in H1.
    destruct (worlds_deceq w w) as [H2|H2].
    +
      discriminate.
    +
      contradict H2.
      reflexivity.
Qed.

Module ex_Model_1.

  Inductive worlds :=
    | pq
    | p
    | q
    | e.

  Scheme Boolean Equality for worlds.

  Instance PQ : Model.
  Proof.
    unshelve econstructor.
    -
      exact worlds.
    -
      intros w1 w2.
      apply is_true.
      apply worlds_beq.
      exact w1.
      exact w2.
    -
      intros w a.
      destruct a as [|[|a']] eqn:H1.
      +
        destruct w eqn:H2.
        exact true.
        exact true.
        exact false.
        exact false.
      +
        destruct w eqn:H2.
        exact true.
        exact false.
        exact true.
        exact false.
      +
        exact false.
    -
      constructor.
      +
        intros []; easy.
      +
        intros [] []; easy.
      +
        intros [] [] []; easy.
    -
      intros [] []; try (left; easy); try (right; easy).
    -
      intros [] [] H1 [|[|]] [|[|]] H2; easy.
  Defined.

End ex_Model_1.
