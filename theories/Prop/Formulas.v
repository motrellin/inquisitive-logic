
From InqLog.Prop Require Export Models.

Class Formula :=
  {
    form : Type;
    support `{Model} : form -> state -> Prop
  }.

Section properties.

  Context `{Formula}.

  Definition persistency_property `{Model} :=
    forall f t s,
      substate t s ->
      support f s ->
      support f t.

  Definition empty_support_property `{Model} :=
    forall f,
      support f empty_state.

  Definition ruling_out `{Model} (s : state) (f : form) :=
    ~ (
      exists t,
        substate t s /\
        consistent t /\
        support f t
        ).

  Definition satisfies `{Model} (w : worlds) (f : form) :=
    support f (singleton w).

  Definition truth_conditional (f : form) :=
    forall `(M : Model) (s : state),
    support f s <->
    forall w,
      s w = true ->
      satisfies w f.

End properties.
