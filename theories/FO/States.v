From InqLog.FO Require Export Models.

From Coq Require Export Morphisms Setoid.

Definition state `{Model} : Type := World -> bool.

Definition state_eq `{Model} : relation state :=
  fun s t =>
  forall w,
    s w = t w.

Instance state_eq_Equiv `{Model} : Equivalence state_eq.
Proof.
  split.
  -
    intros s w.
    reflexivity.
  -
    intros s t H1 w.
    rewrite H1.
    reflexivity.
  -
    intros s t u H1 H2 w.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Definition empty_state `{Model} : state := fun _ => false.

Definition singleton `{Model} (w : World) : state :=
  fun w' =>
  if World_deceq w' w
  then true
  else false.

Proposition singleton_true `{Model} :
  forall w w',
    singleton w w' = true <->
    w' = w.
Proof.
  intros w w'.
  unfold singleton.
  destruct (World_deceq w' w) as [H1|H1].
  all: easy.
Qed.

Proposition singleton_false `{Model} :
  forall w w',
    singleton w w' = false <->
    w' <> w.
Proof.
  intros w w'.
  unfold singleton.
  destruct (World_deceq w' w) as [H1|H1].
  all: easy.
Qed.

Definition consistent `{Model} (s : state) : Prop := exists w, s w = true.

Fact singleton_consistent `{Model} :
  forall w,
    consistent (singleton w).
Proof.
  intros w.
  exists w.
  apply singleton_true.
  reflexivity.
Qed.

Fact empty_state_not_consistent `{Model} :
  forall s,
    state_eq s empty_state ->
    ~ consistent s.
Proof.
  intros s H1 [w H2].
  rewrite H1 in H2.
  discriminate.
Qed.

Definition substate `{Model} : relation state :=
  fun t s =>
  forall w,
    t w = true -> s w = true.

Instance substate_PreOrder `{Model} : PreOrder substate.
Proof.
  constructor.
  -
    intros s w H1.
    exact H1.
  -
    intros s1 s2 s3 H1 H2 w H3.
    apply H2.
    apply H1.
    exact H3.
Qed.

Instance substate_Proper `{Model} : Proper (state_eq ==> state_eq ==> iff) substate.
Proof.
  intros s1 s2 H1 t1 t2 H2.
  unfold substate.
  unfold state_eq in *.
  firstorder.
  -
    rewrite <- H2.
    apply H3.
    rewrite H1.
    exact H4.
  -
    rewrite H2.
    apply H3.
    rewrite <- H1.
    exact H4.
Qed.

Lemma substate_singleton `{Model} :
  forall w t,
    substate t (singleton w) ->
    (
      state_eq t empty_state \/
      state_eq t (singleton w)
    ).
Proof.
  intros w t H1.
  unfold substate in H1.
  unfold empty_state.
  unfold state_eq.
  destruct (t w) eqn:H2.
  -
    right.
    intros w'.
    destruct (t w') eqn:H3.
    +
      symmetry.
      auto.
    +
      symmetry.
      apply singleton_false.
      intros H4.
      subst w'.
      congruence.
  -
    left.
    intros w'.
    destruct (t w') eqn:H3.
    +
      apply H1 in H3 as H4.
      apply singleton_true in H4.
      congruence.
    +
      reflexivity.
Qed.
