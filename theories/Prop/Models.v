Definition atoms := nat.

Class Model :=
  {
    worlds : Type;
    worlds_deceq : forall (w1 w2 : worlds), {w1 = w2} + {w1 <> w2};
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

Definition singleton `{Model} (w : worlds) : state :=
  fun w' => if worlds_deceq w' w then true else false.
