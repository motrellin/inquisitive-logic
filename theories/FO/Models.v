From InqLog.FO Require Export Signatures.

(* Models *)

Class Model `{Signature} :=
  {
    World : Type;
    World_deceq :
      forall (w w' : World),
      {w = w'} + {w <> w'};

    Individual : Type;
    Individual_inh : Individual;

    PInterpretation :
      forall (w : World) (p : PSymb),
        (PAri p -> Individual) ->
        Prop;

    FInterpretation :
      forall (w : World) (f : FSymb),
        (FAri f -> Individual) ->
        Individual;

    rigidity :
      forall (f : FSymb),
        rigid f = true ->
        forall (w w' : World),
          FInterpretation w f = FInterpretation w' f
  }.
