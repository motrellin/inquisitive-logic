From InqLog.FO Require Import Models.

Program Definition two_Worlds_Model `{Signature} : Model :=
  {|
    World := bool;
    Individual := unit;
    Individual_inh := tt;
    PInterpretation := fun w _ _ => if w then True else False;
    FInterpretation := fun _ _ _ => tt
  |}.

Solve All Obligations with (repeat intro; reflexivity).
