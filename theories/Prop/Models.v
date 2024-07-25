Definition atoms := nat.

Class Model :=
  {
    worlds : Type;
    truth_value : worlds -> atoms -> bool
  }.

Definition state `{Model} := worlds -> bool.

Definition substate `{Model} (t s : state) :=
  forall w,
    t w = true ->
    s w = true.

Definition empty_state `{Model} : state := fun _ => false.

Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    s w = true.
