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
    Individual_deceq :
      forall (i i' : Individual),
        {i = i'} + {i <> i'};

    PInterpretation :
      World ->
      forall (p : PSymb),
        (PAri p -> Individual) ->
        bool;

    FInterpretation :
      World ->
      forall (f : FSymb),
        (FAri f -> Individual) ->
        Individual;

    rigidity :
      forall (f : FSymb),
        rigid f = true ->
        forall (w w' : World),
          FInterpretation w f = FInterpretation w' f
  }.
