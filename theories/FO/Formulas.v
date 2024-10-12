From Autosubst Require Export Autosubst.
From Coq Require Import Bool Nat.

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

(* Autosubst-stuff about terms *)

Instance Ids_term `{Signature} : Ids term.
Proof. derive. Defined.

Instance Rename_term `{Signature} : Rename term.
Proof. derive. Defined.

Instance Subst_term `{Signature} : Subst term.
Proof. derive. Defined.

Instance SubstLemmas_term `{Signature} : SubstLemmas term.
Proof. derive. Qed.

(* syntax of first-order formulas including inquisitive operators *)

Inductive form `{Signature} :=
  (* predicate symbols *)
  | Pred : forall (p : PSymb), (PAri p -> term) -> form

  (* propositional connectives *)
  | Bot (v : var) : form
  | Impl : form -> form -> form
  | Conj : form -> form -> form
  | Idisj : form -> form -> form

  (* first-order connectives *)
  | Forall : {bind term in form} -> form
  | Iexists : {bind term in form} -> form.

(* Autosubst-stuff about formulas *)

Instance HSubst_form `{Signature} : HSubst term form.
Proof. derive. Defined.

Instance Ids_form `{Signature} : Ids form.
Proof. derive. Defined.

Instance Rename_form `{Signature} : Rename form.
Proof. derive. Defined.

Instance Subst_form `{Signature} : Subst form.
Proof. derive. Defined.

Instance HSubstLemmas_form `{Signature} : HSubstLemmas term form.
Proof. derive. Qed.

Instance SubstHSubstComp_term_form `{Signature} : SubstHSubstComp term form.
Proof. derive. Qed.

Instance SubstLemmas_form `{Signature} : SubstLemmas form.
Proof. derive. Qed.

(* Other defined connectives *)

Section defined_connectives.

  Context `{Signature}.

  Definition Neg (f : form) := Impl f (Bot 0).
  Definition Top := Neg (Bot 0).
  Definition Disj (f1 f2 : form) := Neg (Conj (Neg f1) (Neg f2)).
  Definition Iff (f1 f2 : form) := Conj (Impl f1 f2) (Impl f2 f1).
  Definition Exists (f : form) := Forall (Neg f).
  Definition Iquest (f : form) := Idisj f (Neg f).

End defined_connectives.

(* Models *)

Class Model `{Signature} :=
  {
    World : Type;
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

(* (Variable) Assignments *)

Definition assignment `{Model} : Type := var -> Individual.

Fixpoint referent `{Model} (t : term) : World -> assignment -> Individual :=
  match t with
  | Var v =>
      fun _ g =>
      g v
  | Func f ari =>
      fun w g =>
      let args :=
        fun arg =>
        referent (ari arg) w g
      in
      FInterpretation w f args
  end.

Definition state `{Model} : Type := World -> bool.

Definition substate `{Model} (t s : state) : Prop :=
  forall w,
    t w = true -> s w = true.

Fixpoint support `{Model} (phi : form) : state -> assignment -> Prop :=
  match phi with
  | Pred p ari =>
      fun s a =>
      forall (w : World),
        s w = true ->
        let args :=
          fun arg =>
          referent (ari arg) w a
        in
        PInterpretation w p args

  | Bot _ =>
      fun s a =>
      forall (w : World),
        s w = false

  | Impl phi1 phi2 =>
      fun s a =>
      forall (t : state),
        substate t s ->
        support phi1 t a ->
        support phi2 t a

  | Conj phi1 phi2 =>
      fun s a =>
      support phi1 s a /\
      support phi2 s a

  | Idisj phi1 phi2 =>
      fun s a =>
      support phi1 s a \/
      support phi2 s a

  | Forall phi1 =>
      fun s a =>
      forall (i : Individual),
        support phi1 s (i .: a)

  | Iexists phi1 =>
      fun s a =>
      exists (i : Individual),
        support phi1 s (i .: a)

  end.
