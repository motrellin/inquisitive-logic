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

Declare Scope model_scope.
Open Scope model_scope.
Infix "=W=" := worlds_eq (at level 70) : model_scope.

Record state `{Model} :=
  {
    state_fun : worlds -> bool;
    state_proper :: Proper (worlds_eq ==> eq) state_fun
  }.

Coercion state_fun : state >-> Funclass. (* Improve readability *)

Definition state_eq `{Model} (s1 s2 : state) : Prop :=
  forall w, s1 w = s2 w.

Infix "=S=" := state_eq (at level 70) : model_scope.

Instance state_eq_equiv : forall `{Model}, Equivalence state_eq.
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
    Proper (state_eq ==> state_eq ==> iff) substate.
Proof.
  intros M s1 s2 H1 t1 t2 H2.
  unfold state_eq, substate in *.
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
    Proper (worlds_eq ==> state_eq) singleton.
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
    s =S= (singleton w) \/
    s =S= empty_state.
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
    w =W= w' <->
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


(** * Examples *)
(** ** Example 1 *)

Module ex_Model_1.

  (** We define a model with four possible worlds and two atoms. *)

  Instance PQ : Model.
  Proof.
    unshelve econstructor.
    -
      (** The type [bool -> bool] has exactly four inhabitants. *)
      exact (bool -> bool).
    -
      intros f g.
      exact (forall b, f b = g b).
    -
      (** Let's define the [truth_value] function. *)
      intros f a.
      (** The type of atoms is [nat], but we only need two atoms which can be
         represented by [0] and [1]. Every other natural number is mapped to
         [false]. *)
      destruct a as [|[|a']] eqn:H1.
      +
        apply f.
        (** Let's encode the atom [0] as [false]. *)
        exact false.
      +
        apply f.
        (** Let's encode the atom [1] as [true]. *)
        exact true.
      +
        (** Every other atom is mapped to [false]. *)
        exact false.
    -
      constructor.
      +
        congruence.
      +
        congruence.
      +
        congruence.
    -
      intros f g.
      try (left; easy).
      destruct
        (f false) eqn:H1,
        (f true) eqn:H2,
        (g false) eqn:H3,
        (g true) eqn:H4.
      all: try (left; intros [|]; congruence).
      all: right; congruence.
    -
      intros f g H1 [|[|]] [|[|]] H2.
      all: congruence.
  Defined.

End ex_Model_1.
