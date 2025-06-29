From InqLog Require Import Seq.

(** * Signature *)

Program Instance signature : Signature :=
  {|
    (**
       As we only want one predicate symbol, we can define [PSymb] to be the singleton type [unit].
     *)
    PSymb := unit;
    (**
       The only existing predicate symbol should be unary, so it needs arity 1.
       This is implemented by the singleton arity type [unit].
       As we only have one predicate symbol, there is no need for a case distinction on [p].
     *)
    PAri := fun _ => unit;
    PAri_enum := fun _ => tt :: nil;
    (**
       As there exists no function symbol, the type of function symbols shall be the empty type [Empty_set].
     *)
    FSymb := Empty_set;
    (**
       Destructing a [f : Empty_set] gives us no object.
       Alternatively, one could also define any type to be [FAri f].
     *)
    FAri := fun f => match f with end;
    FAri_enum := fun _ => nil;
    (**
       As there exists no function symbol, every function symbol can be considered to be rigid.
     *)
    rigid := fun _ => true
  |}.

Next Obligation.
  destruct a.
  left.
  reflexivity.
Qed.

Solve All Obligations with easy.

(** * Syntax *)

Definition Pred' (t : term) :=
  Pred tt (fun arg => t).

Lemma hsubst_Pred' :
  forall t sigma,
    (Pred' t).|[sigma] == Pred' t.[sigma].
Proof.
  intros t sigma.
  simpl.
  red.
  rewrite <- eq_rect_eq_dec; try exact PSymb_EqDec.
  reflexivity.
Qed.
