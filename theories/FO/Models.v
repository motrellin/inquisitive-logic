From InqLog.FO Require Export Signatures.

From Coq Require Export Classical_Prop.

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
    PInterpretation_Proper :: Proper (equiv ==> eq) PInterpretation;

    (**
       We proceed the same way for function symbols.
     *)
    FInterpretation :
      World ->
      forall (f : FSymb),
        (FAri f -> Individual) ->
        Individual;
    FInterpretation_Proper :: Proper (equiv ==> eq) FInterpretation;

    (**
       Lastly, a model needs to ensure [rigidity]. This means,
       that the interpretation of a rigid function symbols
       remains the same in every world.
     *)
    rigidity :
      forall (f : FSymb),
        rigid f = true ->
        forall (w w' : World),
          FInterpretation w f = FInterpretation w' f
  }.


(* TODO Examples? *)
