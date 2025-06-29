From InqLog Require Export SetoidLib.

(**
   We start by defining the class of [Signature]s.
   A _signature_ consists of a set of _predicate symbols_ (captured by the type [PSymb]) and a set of _function symbols_ (captured by the type [FSymb]).
   Each symbol has an finite _arity_ (type), which is assigned by the functions [PAri] and [FAri].
   The finiteness is captured by enumerations [PAri_enum] and [FAri_enum] whose characterization are captured by [PAri_enum_charac] and [FAri_enum_charac].

   We also want to have decidable (standard) equality for both [PSymb] and [FSymb] which is captured by [PSymb_EqDec] and [FSymb_EqDec].

   In addition, we need a boolean predicate [rigid] which tells us for every function symbol whether it is [rigid] or not.
   A function symbol shall be called [rigid] if its interpretation is independent from a concrete world.

   This whole definition is based on Ciardelli's work.
 *)

Class Signature :=
  {
    PSymb : Type;
    PSymb_EqDec :: EqDec (eq_setoid PSymb);
    PAri : PSymb -> Type;
    PAri_enum : forall p, list (PAri p);
    PAri_enum_charac : forall p a, In a (PAri_enum p);
    FSymb : Type;
    FSymb_EqDec :: EqDec (eq_setoid FSymb);
    FAri : FSymb -> Type;
    FAri_enum : forall f, list (FAri f);
    FAri_enum_charac : forall f a, In a (FAri_enum f);
    rigid : FSymb -> bool
  }.
