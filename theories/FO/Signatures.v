From InqLog Require Export SetoidLib.

(**
   We start by defining the class of [Signature]s. A _Signature_ consists of a
   set of _predicate symbols_ (captured by the type [PSymb]) and a set of
   _function symbols_ (captured by the type [FSymb]). Each symbol has an
   _arity_ (type), which is assigned by the functions [PAri] and [FAri].

   In addition, we need a boolean predicate [rigid], which tells us for every
   function symbol, whether it is rigid or not.

   This whole definition is taken from Ciardelli 2022.
 *)

Class Signature :=
  {
    PSymb : Type;
    PSymb_EqDec :: EqDec (eq_setoid PSymb);
    PAri : PSymb -> Type; (* TODO: Where comes this idea from? *)
    PAri_enum : forall p, list (PAri p);
    PAri_enum_charac : forall p a, In a (PAri_enum p);
    FSymb : Type;
    FSymb_EqDec :: EqDec (eq_setoid FSymb);
    FAri : FSymb -> Type;
    FAri_enum : forall f, list (FAri f);
    FAri_enum_charac : forall f a, In a (FAri_enum f);
    rigid : FSymb -> bool (* TODO: Add an explanation of rigidity. *)
  }.

(**
   Here are a few examples:
 *)

Module Signature_single_unary_predicate.

  Program Instance signature : Signature :=
    {|
      (**
         As we only want one predicate symbol, we need [PSymb] to be the
         singleton type [unit].
       *)
      PSymb := unit;
      (**
         The only existing predicate symbol should be unary, so it needs arity
         1. This is implemented by the singleton arity type [unit].
       *)
      PAri := fun p => match p with tt => unit end;
      (**
         As there exists no function symbol, the type of function symbols shall
         be the empty type [Empty_set].
       *)
      FSymb := Empty_set;
      (**
         Destructing a [f : Empty_set] gives us no object.
       *)
      FAri := fun f => match f with end;
      (**
         As there exists no function symbol, every function symbol is rigid.
       *)
      rigid := fun _ => true
    |}.

  Next Obligation.
    destruct p.
    exact (tt :: nil).
  Defined.

  Next Obligation.
    destruct p.
    destruct a.
    left.
    reflexivity.
  Qed.

  Solve All Obligations with easy.

End Signature_single_unary_predicate.

Module Signature_single_binary_predicate.

  Program Instance signature : Signature :=
    {|
      PSymb := unit;
      (**
         The only difference to the first example is the arity of the only
         predicate symbol which is now represented by the Type [bool] which
         consists of exact two inhabitants.
       *)
      PAri := fun p => match p with tt => bool end;
      FSymb := Empty_set;
      FAri := fun f => match f with end;
      rigid := fun _ => true
    |}.

  Next Obligation.
    destruct p.
    exact (true :: false :: nil).
  Defined.

  Next Obligation.
    destruct p.
    destruct a.
    -
      left; reflexivity.
    -
      right; left; reflexivity.
  Qed.

  Solve All Obligations with easy.

End Signature_single_binary_predicate.
