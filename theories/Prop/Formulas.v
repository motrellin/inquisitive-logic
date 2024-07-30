
From InqLog.Prop Require Export Models.

(** * Formulas

We want to define different formula sets.
Such a set is a type class [Formula] with a type [form] (_Syntax_) and
   support semantics [support : Model -> form -> state -> Prop].
 *)

Class Formula :=
  {
    form : Type;
    support `{Model} : form -> state -> Prop
  }.

Notation "s |= f" := (support f s) (at level 70) : state_scope.

(** ** Various properties *)

Section properties.

  Context `{Formula}.

  (** *** Persistency *)

  Definition persistency_property `{Model} :=
    forall f t s,
      substate t s ->
      s |= f ->
      t |= f.

  (** *** Empty Support *)

  Definition empty_support_property `{Model} : Prop :=
    forall f,
      empty_state |= f.

End properties.

(** ** Some useful definitions *)

Section definitions.

  Context `{Formula}.

  (** *** Ruling out a fomula *)

  Definition ruling_out `{Model} (s : state) (f : form) :=
    ~ (
      exists t,
        substate t s /\
        consistent t /\
        t |= f
        ).

  (** *** Satisfaction *)

  Definition satisfies `{Model} (w : worlds) (f : form) :=
    (singleton w) |= f.

  (** *** Truth conditional formula *)

  Definition truth_conditional (f : form) :=
    forall `(M : Model) (s : state),
    s |= f <->
    forall w,
      s w = true ->
      satisfies w f.

End definitions.
