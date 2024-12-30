From InqLog.FO Require Export Signatures.

From Autosubst Require Export Autosubst.

From Coq Require Export Bool FunctionalExtensionality.

(** * Terms

   Let's start by recursively defining _terms_ over a
   signature. A term is either a _variable_ or an application
   of a function symbol [f] to some terms, respecting
   [FAri f]. This is done via a function [FAri f -> term].
 *)

Inductive term `{Signature} :=
  | Var : var -> term
  | Func : forall (f : FSymb), (FAri f -> term) -> term.

Print var.
(**
   [var] is defined as [nat] via [Autosubst] which is a
   framework for binders in terms using de Bruijn indices.

   To use Autosubst efficiently, we need to define some
   instances.
 *)

Instance Ids_term `{Signature} : Ids term.
Proof. derive. Defined.

Instance Rename_term `{Signature} : Rename term.
Proof. derive. Defined.

Instance Subst_term `{Signature} : Subst term.
Proof. derive. Defined.

Instance SubstLemmas_term `{Signature} : SubstLemmas term.
Proof. derive. Qed.

Section unnamed_helpers.

  Context `{Signature}.
  Context {X : Type}.
  Context (a : var -> X).
  Context (i : X).
  Context (sigma : var -> var).

  Lemma unnamed_helper_Syntax_1 :
    i .: sigma >>> a = (upren sigma) >>> i .: a.
  Proof.
    apply functional_extensionality.
    destruct x as [|x'].
    all: autosubst.
  Qed.

End unnamed_helpers.

Fixpoint rigid_term `{Signature} (t : term) : Prop :=
  match t with
  | Var x => True
  | Func f args =>
      rigid f = true /\
      forall arg,
        rigid_term (args arg)
  end.

(** * Formulas
   Next step is to recursively define _formulas_ over a
   signature. A [form]ula is either
   - an application of a predicate symbol [p] to some terms,
     respecting [PAri p], which is done via a function
     [PAri p -> term],
   - Falsum, which is represented by [Bot],
   - an _Implication_, Conjunction or Inquisivite Disjunction,
   - an all-quantified formula or
   - an inquisivite existential-quantified formula.

   Note, that binding is done by de Bruijn indices,
   implemented via the libary [Autosubst]. For example,
   we will just write [Forall phi] (for a [form]ula [phi])
   where the variable [0] is bounded inside of [phi].

   For technical reasons, we also define [Bot : var -> form].
 *)

Inductive form `{Signature} :=
  (* predicate symbols *)
  | Pred : forall (p : PSymb), (PAri p -> term) -> form

  (* propositional connectives *)
  | Bot : var -> form
  | Impl : form -> form -> form
  | Conj : form -> form -> form
  | Idisj : form -> form -> form

  (* first-order connectives *)
  | Forall : {bind term in form} -> form
  | Iexists : {bind term in form} -> form.

(**
   Let us introduce some notation. It is not necessary to
   understand the technical details. For more information,
   please refer to the Coq documentation.
 *)

Declare Custom Entry form.
Declare Scope form_scope.

Notation "<{ phi }>" := phi
  (at level 0, phi custom form at level 99)
  : form_scope.
Notation "( x )" := x
  (in custom form, x at level 99)
  : form_scope.
Notation "x" := x
  (in custom form at level 0, x constr at level 0)
  : form_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom form at level 0,
  only parsing,
  f constr at level 0,
  x constr at level 9,
  y constr at level 9)
  : form_scope.

Notation "phi -> psi" := (Impl phi psi)
  (in custom form at level 99, right associativity)
  : form_scope.

Notation "phi /\ psi" := (Conj phi psi)
  (in custom form at level 80, right associativity)
  : form_scope.

Notation "phi \\/ psi" := (Idisj phi psi)
  (in custom form at level 86, right associativity)
  : form_scope.

Notation "'forall' phi" := (Forall phi)
  (in custom form at level 200, right associativity)
  : form_scope.

Notation "'iexists' phi" := (Iexists phi)
  (in custom form at level 201, right associativity)
  : form_scope.

Open Scope form_scope.

(**
   And again, we need to derive some [Autosubst]-[Instance]s.
 *)

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

(** ** Defined connectives

   We define some typical connectives via our definition
   of [form], as typical. We also add some notation for them.
 *)

Definition Neg `{Signature} (phi : form) :=
  <{ phi -> (Bot 0) }>.

Notation "~ phi" := (Neg phi)
  (in custom form at level 75, right associativity)
  : form_scope.

Definition Top `{Signature} :=
  <{~ (Bot 0)}>.

Definition Disj `{Signature} (phi1 phi2 : form) :=
  <{ ~ (~ phi1 /\ ~ phi2) }>.

Notation "phi \/ psi" := (Disj phi psi)
  (in custom form at level 85, right associativity)
  : form_scope.

Definition Iff `{Signature} (phi1 phi2 : form) :=
  <{ (phi1 -> phi2) /\ (phi2 -> phi1) }>.

Notation "phi <-> psi" := (Iff phi psi)
  (in custom form at level 95, right associativity)
  : form_scope.

Definition Exists `{Signature} (phi : form) :=
  <{ ~ forall (~ phi) }>.

Notation "'exists' phi" := (Exists phi)
  (in custom form at level 200, right associativity)
  : form_scope.

Definition Iquest `{Signature} (phi : form) :=
  <{ phi \\/ ~ phi }>.

Notation "? phi" := (Iquest phi)
  (in custom form at level 76, right associativity)
  : form_scope.

(** ** Example formulas

   We can now use our new syntax notation to define some
   example formulas for illustration purpose.

 *)

Example iquest_p `{Signature} (p : PSymb) (args : PAri p -> term) : form :=
  <{ ? Pred p args }>.

Example DNE `{Signature} (phi : form) : form :=
  <{ (~ (~ phi)) -> phi }>.

(** ** Classic formulas

   We want to introduce the notion of a _classical formula_.
   A formula is called _classical_, iff it doesn't contain
   inquisitive disjunction or inquisitive existential
   quantifiers.
 *)

Fixpoint classical `{Signature} (phi : form) : bool :=
  match phi with
  | Pred p ari =>
      true

  | Bot v =>
      true

  | Impl phi1 phi2 =>
      classical phi1 && classical phi2

  | Conj phi1 phi2 =>
      classical phi1 && classical phi2

  | Idisj phi1 phi2 =>
      false

  | Forall phi1 =>
      classical phi1

  | Iexists phi1 =>
      false

  end.

Example iquest_p_not_classical `{Signature} :
  forall p args,
    classical (iquest_p p args) = false.
Proof.
  reflexivity.
Qed.

Example DNE_classic `{Signature} :
  forall phi,
    classical (DNE phi) = classical phi.
Proof.
  intros phi.
  simpl.
  destruct (classical phi).
  all: reflexivity.
Qed.

(**
   For every formula, we can construct a [classical] variant
   of it by replacing inquisitive connectives by their
   standard variant.
 *)
Fixpoint classical_variant `{Signature} (phi : form) : form :=
  match phi with
  | Pred p ari =>
      Pred p ari

  | Bot v =>
      Bot v

  | Impl phi1 phi2 =>
      Impl (classical_variant phi1) (classical_variant phi2)

  | Conj phi1 phi2 =>
      Conj (classical_variant phi1) (classical_variant phi2)

  | Idisj phi1 phi2 =>
      Disj (classical_variant phi1) (classical_variant phi2)

  | Forall phi1 =>
      Forall (classical_variant phi1)

  | Iexists phi1 =>
      Exists (classical_variant phi1)

  end.

(**
   We can verify [classical_variant] by the following
   proposition.
 *)

Proposition classical_variant_is_classical `{Signature} :
  forall phi,
    classical (classical_variant phi) = true.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: simpl.
  all: try rewrite IH1.
  all: try rewrite IH2.
  all: reflexivity.
Qed.
