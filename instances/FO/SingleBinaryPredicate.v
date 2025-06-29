From InqLog.FO Require Import Truth.

(** * Signature *)

Program Instance signature : Signature :=
  {|
    PSymb := unit;
    PAri := fun _ => bool;
    PAri_enum := fun _ => true :: false :: nil;
    FSymb := Empty_set;
    FAri := fun f => match f with end;
    rigid := fun _ => true
  |}.

Next Obligation.
  destruct a.
  -
    left; reflexivity.
  -
    right; left; reflexivity.
Qed.

Solve All Obligations with easy.

(** * Syntax *)

Definition Pred' (t1 t2 : term) :=
  Pred tt (fun arg => if arg then t1 else t2).

Lemma hsubst_Pred' :
  forall t1 t2 sigma,
    (Pred' t1 t2).|[sigma] == Pred' t1.[sigma] t2.[sigma].
Proof.
  intros t1 t2 sigma.
  simpl.
  red.
  rewrite <- eq_rect_eq_dec; try exact PSymb_EqDec.
  intros [|].
  all: reflexivity.
Qed.
