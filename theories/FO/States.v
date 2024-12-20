From InqLog.FO Require Export Models.

From Coq Require Export Morphisms Setoid.

(** * Basic definitions

   We now introduce the notion of a [state] which is just a
   set of worlds in a model.
 *)

Definition state `{Model} : Type := World -> bool.

(**
   As we typically just care whether two states behave the
   same, we introduce this as a relation [state_eq], which
   is indeed an equivalence relation.
 *)
Definition state_eq `{Model} : relation state :=
  fun s t =>
  forall w,
    s w = t w.

Instance state_eq_Equiv `{Model} : Equivalence state_eq.
Proof.
  split.
  -
    (* Reflexivity *)
    intros s w.
    reflexivity.
  -
    (* Symmetry *)
    intros s t H1 w.
    rewrite H1.
    reflexivity.
  -
    (* Transitivity *)
    intros s t u H1 H2 w.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

(** * Example states *)
(** ** The empty state *)

Definition empty_state `{Model} : state := fun _ => false.

(** ** Singleton states *)

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

(** ** Complement states *)

Definition complement `{Model} (s : state) : state :=
  fun w =>
  negb (s w).

Fact complement_true `{Model} :
  forall s w,
    complement s w = true <->
    s w = false.
Proof.
  intros s w.
  unfold complement.
  destruct (s w) eqn:H1.
  all: easy.
Qed.

Fact complement_false `{Model} :
  forall s w,
    complement s w = false <->
    s w = true.
Proof.
  intros s w.
  unfold complement.
  destruct (s w) eqn:H1.
  all: easy.
Qed.

Fact complement_complement `{Model} :
  forall s,
    state_eq (complement (complement s)) s.
Proof.
  intros s w.
  destruct (s w) eqn:H1.
  -
    rewrite complement_true.
    rewrite complement_false.
    exact H1.
  -
    rewrite complement_false.
    rewrite complement_true.
    exact H1.
Qed.

(** * Consistent states *)

Definition consistent `{Model} (s : state) : Prop := exists w, s w = true.

Fact empty_state_not_consistent `{Model} :
  forall s,
    state_eq s empty_state ->
    ~ consistent s.
Proof.
  intros s H1 [w H2].
  rewrite H1 in H2.
  discriminate.
Qed.

Fact singleton_consistent `{Model} :
  forall w,
    consistent (singleton w).
Proof.
  intros w.
  exists w.
  apply singleton_true.
  reflexivity.
Qed.

(** * Substates *)

Definition substate `{Model} : relation state :=
  fun t s =>
  forall w,
    t w = true -> s w = true.

Lemma substate_contrapos `{Model} :
  forall s t w,
    substate t s ->
    s w = false ->
    t w = false.
Proof.
  intros s t w H1 H2.
  destruct (t w) eqn:H3; try reflexivity.
  apply H1 in H3.
  congruence.
Qed.

(**
   We will now see, that [substate] is a [PreOrder].
 *)
Print PreOrder.
(**
   A [PreOrder] is a [reflexive] and [transitive] [relation],
   at least, if we follow the way, Coq defines it as such.
 *)
Instance substate_PreOrder `{Model} : PreOrder substate.
Proof.
  constructor.
  -
    (* Reflexivity *)
    intros s w H1.
    exact H1.
  -
    (* Transitivity *)
    intros s1 s2 s3 H1 H2 w H3.
    apply H2.
    apply H1.
    exact H3.
Qed.

(**
   We can also prove that [state_eq] is a congruence relation
   with respect to [substate]:
 *)
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

Lemma substate_complement `{Model} :
  forall s t,
    substate t s <->
    substate (complement s) (complement t).
Proof.
  intros s t.
  unfold complement.
  split.
  all: intros H1 w H2.
  -
    destruct (t w) eqn:H3; try reflexivity.
    apply H1 in H3.
    congruence.
  -
    destruct (s w) eqn:H3; try reflexivity.
    specialize (H1 w).
    simpl in H1.
    rewrite H2,H3 in H1.
    auto.
Qed.
