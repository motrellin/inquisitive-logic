From InqLog.FO Require Export Signatures.

(**
   To interpret formulas, we need a suitable model. We will
   define them as follows:
 *)

Class Model `{Signature} :=
  {
    (**
       First of all, we need a set of _worlds_ with _decidable
       equality_.
     *)
    World : Type;
    World_Setoid :: Setoid World;
    World_Setoid_EqDec :: EqDec World_Setoid;

    (**
       Second, a _non-empty_ set of _individuals_ with
       decidable equality is need.
     *)
    Individual : Type;
    Individual_inh : Individual;
    Individual_deceq :
      forall (i i' : Individual),
        {i = i'} + {i <> i'};

    (**
       Next, we need to interpret predicate symbols [p] in
       every possible world. Remember, [PAri p] is the arity
       type of [p], per intuition the number of arguments of
       [p]. As one typically interprets predicate symbols with
       relations on the set of individuals, we need a function
       of type [PAri p -> Individual] to reflect this
       intuition.

       One should also note the codomain of [PInterpretation]
       which is [bool]. By this, we ensure decidability of
       [PInterpretation w] in every world [w].
     *)
    PInterpretation :
      World ->
      forall (p : PSymb),
        (PAri p -> Individual) ->
        bool;
    PInterpretation_Proper_outer ::
      Proper (equiv ==> eq) PInterpretation;
    PInterpretation_Proper_inner ::
      forall w p,
        Proper (ext_eq ==> eq) (PInterpretation w p);

    (**
       We proceed the same way for function symbols.
     *)
    FInterpretation :
      World ->
      forall (f : FSymb),
        (FAri f -> Individual) ->
        Individual;
    FInterpretation_Proper_outer ::
      Proper (equiv ==> eq) FInterpretation;
    FInterpretation_Proper_inner ::
      forall w f,
        Proper (ext_eq ==> eq) (FInterpretation w f);

    (**
       Lastly, a model needs to ensure [rigidity]. This means,
       that the interpretation of a rigid function symbols
       remains the same in every world.
     *)
    rigidity :
      forall (f : FSymb),
        rigid f = true ->
        forall (w w' : World),
          FInterpretation w f == FInterpretation w' f
  }.


(* TODO Examples? *)

Program Definition two_Worlds_Model `{Signature} : Model :=
  {|
    World := bool;
    Individual := unit;
    Individual_inh := tt;
    PInterpretation := fun w _ _ => w;
    FInterpretation := fun _ _ _ => tt
  |}.

Next Obligation.
  decide equality.
Qed.

Solve All Obligations with (repeat intro; reflexivity).

(** * Variable Assignments

   We refer to a variable assignment function by the short
   name [assignment].
 *)

Definition assignment `{Model} : Type :=
  var -> Individual.

Definition pointed_assignment `{Model} : assignment :=
  fun _ => Individual_inh.
