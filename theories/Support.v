Definition atoms := nat.

Class Model :=
  {
    possible_worlds : Type;
    truth_value : possible_worlds -> atoms -> bool
  }.

Definition state `{Model} := possible_worlds -> Prop.

Definition empty_state `{Model} : state := fun _ => False.

Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    s w.

Lemma consistent_state_not_empty `{Model} :
  forall s,
    consistent s ->
    s <> empty_state.
Proof.
  intros s H1 H2.
  subst.
  destruct H1 as [w H1].
  assumption.
Qed.
