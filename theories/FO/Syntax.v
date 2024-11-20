From InqLog.FO Require Export Signatures.

From Autosubst Require Export Autosubst.

(** * Terms *)

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

(** * Formulas *)

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
  (in custom form at level 70, right associativity)
  : form_scope.

Notation "phi /\ psi" := (Conj phi psi)
  (in custom form at level 60, right associativity)
  : form_scope.

Notation "phi \\/ psi" := (Idisj phi psi)
  (in custom form at level 65, right associativity)
  : form_scope.

Notation "'forall' phi" := (Forall phi)
  (in custom form at level 85, right associativity)
  : form_scope.

Notation "'iexists' phi" := (Iexists phi)
  (in custom form at level 90, right associativity)
  : form_scope.

Open Scope form_scope.

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

(** ** Defined connectives *)

Definition Neg `{Signature} (phi : form) :=
  <{ phi -> (Bot 0) }>.

Notation "~ phi" := (Neg phi)
  (in custom form at level 55, right associativity)
  : form_scope.

Definition Top `{Signature} :=
  <{~ (Bot 0)}>.

Definition Disj `{Signature} (phi1 phi2 : form) :=
  <{ ~ (~ phi1 /\ ~ phi2) }>.

Notation "phi \/ psi" := (Disj phi psi)
  (in custom form at level 66, right associativity)
  : form_scope.

Definition Iff `{Signature} (phi1 phi2 : form) :=
  <{ (phi1 -> phi2) /\ (phi2 -> phi1) }>.

Notation "phi <-> psi" := (Iff phi psi)
  (in custom form at level 85, right associativity)
  : form_scope.

Definition Exists `{Signature} (phi : form) :=
  <{ ~ forall (~ phi) }>.

Notation "'exists' phi" := (Exists phi)
  (in custom form at level 91, right associativity)
  : form_scope.

Definition Iquest `{Signature} (phi : form) :=
  <{ phi \\/ ~ phi }>.

Notation "? phi" := (Iquest phi)
  (in custom form at level 56, right associativity)
  : form_scope.

(** ** Example formulas *)

Example DNE `{Signature} (phi : form) : form :=
  <{ (~ (~ phi)) -> phi }>.

(** ** Classic formulas *)

Fixpoint classic `{Signature} (phi : form) : bool :=
  match phi with
  | Pred p ari =>
      true

  | Bot v =>
      true

  | Impl phi1 phi2 =>
      classic phi1 && classic phi2

  | Conj phi1 phi2 =>
      classic phi1 && classic phi2

  | Idisj phi1 phi2 =>
      false

  | Forall phi1 =>
      classic phi1

  | Iexists phi1 =>
      false

  end.

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

Proposition classical_variant_is_classic `{Signature} :
  forall phi,
    classic (classical_variant phi) = true.
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
