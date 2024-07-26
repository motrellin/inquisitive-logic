From Coq Require Export RelationClasses Morphisms Setoid.

Definition atoms := nat.

Class Model :=
  {
    worlds : Type;
    worlds_deceq : forall (w1 w2 : worlds), {w1 = w2} + {w1 <> w2};
    truth_value : worlds -> atoms -> bool
  }.

Definition state `{Model} := worlds -> bool.
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

Definition empty_state `{Model} : state := fun _ => false.

Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    s w = true.

Definition singleton `{Model} (w : worlds) : state :=
  fun w' => if worlds_deceq w' w then true else false.

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
      destruct (worlds_deceq w' w).
      *
        reflexivity.
      *
        symmetry.
        auto.
    +
      destruct (worlds_deceq w' w).
      *
        subst w'.
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
      destruct (worlds_deceq w' w).
      *
        subst w'.
        congruence.
      *
        discriminate.
    +
      reflexivity.
Qed.
