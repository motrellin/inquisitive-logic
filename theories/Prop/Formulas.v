
From InqLog.Prop Require Export Models.

Class Formula :=
  {
    form : Type;
    support `{Model} : form -> state -> Prop
  }.

Notation "s |= f" := (support f s) (at level 70) : state_scope.

Section properties.

  Context `{Formula}.

  Definition persistency_property `{Model} :=
    forall f t s,
      substate t s ->
      s |= f ->
      t |= f.

  Definition empty_support_property `{Model} :=
    forall f,
      empty_state |= f.

  Definition ruling_out `{Model} (s : state) (f : form) :=
    ~ (
      exists t,
        substate t s /\
        consistent t /\
        t |= f
        ).

  Definition satisfies `{Model} (w : worlds) (f : form) :=
    (singleton w) |= f.

  Definition truth_conditional (f : form) :=
    forall `(M : Model) (s : state),
    s |= f <->
    forall w,
      s w = true ->
      satisfies w f.

End properties.
