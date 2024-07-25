Definition atoms := nat.

Class Model :=
  {
    possible_worlds : Type;
    some_world : possible_worlds;
    truth_value : possible_worlds -> atoms -> bool
  }.

Definition state `{Model} := possible_worlds -> bool.

Definition substate `{Model} (t s : state) :=
  forall w,
    t w = true ->
    s w = true.

Definition empty_state `{Model} : state := fun _ => false.

Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    s w = true.
