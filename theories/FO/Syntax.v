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

Section defined_connectives.

  Context `{Signature}.

  Definition Neg (phi : form) := Impl phi (Bot 0).
  Definition Top := Neg (Bot 0).
  Definition Disj (phi1 phi2 : form) := Neg (Conj (Neg phi1) (Neg phi2)).
  Definition Iff (phi1 phi2 : form) := Conj (Impl phi1 phi2) (Impl phi2 phi1).
  Definition Exists (phi : form) := Neg (Forall (Neg phi)).
  Definition Iquest (phi : form) := Idisj phi (Neg phi).

End defined_connectives.

(** ** Example formulas *)

Example DNE `{Signature} (phi : form) : form := Impl (Neg (Neg phi)) phi.

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
