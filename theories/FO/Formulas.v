From Autosubst Require Export Autosubst.

(* Signatures *)

Class Signature :=
  {
    PSymb : Type;
    PAri : PSymb -> Type;
    FSymb : Type;
    FAri : FSymb -> Type;
    rigid : FSymb -> bool
  }.

(* Definition of terms *)

Inductive term `{Signature} :=
  | Var : var -> term
  | Func : forall (f : FSymb), (FAri f -> term) -> term.

(* syntax of first-order formulas including inquisitive operators *)

Inductive form `{Signature} :=
  (* predicate symbols *)
  | Pred : forall (p : PSymb), (PAri p -> term) -> form

  (* propositional connectives *)
  | Bot : form
  | Impl : form -> form -> form
  | Conj : form -> form -> form
  | Idisj : form -> form -> form

  (* first-order connectives *)
  | Forall : {bind term in form} -> form
  | Iexists : {bind term in form} -> form.
