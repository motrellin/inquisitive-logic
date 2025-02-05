From InqLog Require Export ListBib.
From InqLog.FO Require Export Signatures.

From Autosubst Require Export Autosubst.

From Coq Require Export Bool FunctionalExtensionality Eqdep_dec.

(** * Terms

   Let's start by recursively defining _terms_ over a
   signature. A term is either a _variable_ or an application
   of a function symbol [f] to some terms, respecting
   [FAri f]. This is done via a function [FAri f -> term].
 *)

Inductive term `{Signature} :=
  | Var : var -> term
  | Func : forall (f : FSymb), (FAri f -> term) -> term.

(** ** Decidable Equality

   As [Func] has a dependent type, it is problematic to use
   standard equality to syntactically compare [term]s.
   That's why we define a suitable decidable equivalence
   relation on terms to which we will refer as equality on
   terms. The definition of this relation [term_eq] is
   rather complex so we split its definition up in
   two parts.
 *)

Definition term_eq_Func_Func_EqDec
  `{S : Signature}
  (rec : relation term)
  (f1 : FSymb)
  (args1 : FAri f1 -> term)
  (f2 : FSymb)
  (args2 : FAri f2 -> term)
  (is_equal : (f1 == f2)%type) : Prop :=

  eq_rect
  f1
  (fun f => (FAri f -> term) -> Prop)
  (fun args =>
    forall arg,
      rec (args1 arg) (args arg)
  )
  f2
  is_equal
  args2.

Fixpoint term_eq `{S : Signature} (t : term) : term -> Prop :=
  match t with
  | Var x1 =>
      fun t2 =>
      match t2 with
      | Var x2 => (x1 == x2)%type
      | _ => False
      end
  | Func f1 args1 =>
      fun t2 =>
      match t2 with
      | Func f2 args2 =>
          match equiv_dec f1 f2 with
          | left is_equal =>
              term_eq_Func_Func_EqDec term_eq f1 args1 f2 args2 is_equal
          | _ => False
          end
      | _ => False
      end
  end.

Instance term_eq_Equiv `{Signature} : Equivalence term_eq.
Proof with (try (now firstorder) + congruence + exact FSymb_EqDec).
  constructor.
  -
    intros t.
    induction t as [x|f args IH]...

    simpl.
    destruct (f == f)...
    rewrite UIP_dec with (p2 := eq_refl)...
  -
    intros t.
    induction t as [x1|f1 args1 IH].
    all: intros [x2|f2 args2] H1...

    simpl in *.
    destruct (f1 == f2), (f2 == f1)...
    simpl in *.
    subst.
    rewrite UIP_dec with (p2 := eq_refl)...
  -
    intros t.
    induction t as [x1|f1 args1 IH].
    all: intros [x2|f2 args2] [x3|f3 args3] H1 H2...

    simpl in *.
    destruct (f1 == f2), (f2 == f3), (f1 == f3)...
    simpl in *.
    subst.
    rewrite UIP_dec with (p2 := eq_refl)...
Qed.

Print Assumptions term_eq_Equiv.

Program Instance term_Setoid `{Signature} : Setoid term.

Instance term_EqDec `{Signature} : EqDec term_Setoid.
Proof with (try (right; easy)).
  intros t1.
  induction t1 as [x1|f1 args1 IH].
  all: intros [x2|f2 args2]...
  -
    destruct (PeanoNat.Nat.eq_dec x1 x2) as [H1|H1].
    all: left + right; congruence.
  -
    unfold complement in *.
    simpl in *.
    destruct (f1 == f2)...
    simpl in *.
    subst f2.
    apply finite_choice with (xs := FAri_enum f1).
    all: intro.
    all: apply FAri_enum_charac + apply IH.
Qed.

Print Assumptions term_EqDec.

(** ** Variables and Substitutions *)

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

(** ** Rigidity *)

Fixpoint rigid_term `{Signature} (t : term) : Prop :=
  match t with
  | Var x => True
  | Func f args =>
      rigid f = true /\
      forall arg,
        rigid_term (args arg)
  end.

Lemma unnamed_helper_Syntax_2 `{Signature} :
  forall t (sigma : var -> term),
  (forall x, rigid_term (sigma x)) ->
    rigid_term t ->
    rigid_term t.[sigma].
Proof.
  induction t as [x|f args IH].
  -
    autosubst.
  -
    intros sigma H1 [H2 H3].
    split; eauto.
Qed.

Lemma unnamed_helper_Syntax_3 `{Signature} :
  forall sigma,
    (forall x, rigid_term (sigma x)) ->
    forall x,
      rigid_term (up sigma x).
Proof.
  intros sigma H1 [|x'].
  -
    exact I.
  -
    asimpl.
    apply unnamed_helper_Syntax_2.
    +
      easy.
    +
      apply H1.
Qed.

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

Fixpoint form_eq `{Signature} (f : form) : form -> Prop.
Proof.
  destruct f as
  [p1 args1
  |?
  |f1 f2
  |f1 f2
  |f1 f2
  |f1
  |f1
  ] eqn:eq1.
  all: intros f'.
  all: destruct f' as
  [p2 args2
  |?
  |f3 f4
  |f3 f4
  |f3 f4
  |f3
  |f3
  ] eqn:eq2.
  -
    destruct (p1 == p2) as [H1|H1].
    +
      simpl in H1.
      subst p2.
      exact (forall arg, term_eq (args1 arg) (args2 arg)).
    +
      exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact True.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact (form_eq _ f1 f3 /\ form_eq _ f2 f4).
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact (form_eq _ f1 f3 /\ form_eq _ f2 f4).
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact (form_eq _ f1 f3 /\ form_eq _ f2 f4).
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact (form_eq _ f1 f3).
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact False.
  -
    exact (form_eq _ f1 f3).
Defined.

Instance form_eq_Equiv `{Signature} : Equivalence form_eq.
Proof.
Admitted.

Program Instance form_Setoid `{Signature} : Setoid form.

Instance form_EqDec `{Signature} : EqDec form_Setoid.
Proof.
  red.
Admitted.

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

Example EM `{Signature} (phi : form) : form :=
  <{phi \/ ~ phi}>.

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
  | Pred p args =>
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

Fact classical_Pred `{Signature} :
  forall p args,
    classical (Pred p args) = true.
Proof.
  reflexivity.
Qed.

Fact classical_Bot `{Signature} :
  forall x,
    classical (Bot x) = true.
Proof.
  reflexivity.
Qed.

Fact classical_Impl `{Signature} :
  forall phi psi,
    classical <{phi -> psi}> = classical phi && classical psi.
Proof.
  reflexivity.
Qed.

Fact classical_Conj `{Signature} :
  forall phi psi,
    classical <{phi /\ psi}> = classical phi && classical psi.
Proof.
  reflexivity.
Qed.

Fact classical_Idisj `{Signature} :
  forall phi psi,
    classical <{phi \\/ psi}> = false.
Proof.
  reflexivity.
Qed.

Fact classical_Forall `{Signature} :
  forall phi,
    classical <{forall phi}> = classical phi.
Proof.
  reflexivity.
Qed.

Fact classical_Iexists `{Signature} :
  forall phi,
    classical <{iexists phi}> = false.
Proof.
  reflexivity.
Qed.

Lemma classical_Neg `{Signature} :
  forall phi,
    classical <{~ phi}> = classical phi.
Proof.
  intros phi.
  unfold Neg.
  rewrite classical_Impl.
  rewrite classical_Bot.
  rewrite andb_true_r.
  reflexivity.
Qed.

Lemma classical_Top `{Signature} :
  classical Top = true.
Proof.
  unfold Top.
  rewrite classical_Neg.
  rewrite classical_Bot.
  reflexivity.
Qed.

Lemma classical_Disj `{Signature} :
  forall phi psi,
    classical <{phi \/ psi}> = classical phi && classical psi.
Proof.
  intros phi psi.
  unfold Disj.
  rewrite classical_Neg.
  rewrite classical_Conj.
  do 2 rewrite classical_Neg.
  reflexivity.
Qed.

Lemma classical_Iff `{Signature} :
  forall phi psi,
    classical <{phi <-> psi}> = classical phi && classical psi.
Proof.
  intros phi psi.
  unfold Iff.
  rewrite classical_Conj.
  do 2 rewrite classical_Impl.
  rewrite andb_comm with
    (b1 := classical psi)
    (b2 := classical phi).
  rewrite andb_diag.
  reflexivity.
Qed.

Lemma classical_Exists `{Signature} :
  forall phi,
    classical <{exists phi}> = classical phi.
Proof.
  intros phi.
  unfold Exists.
  rewrite classical_Neg.
  rewrite classical_Forall.
  rewrite classical_Neg.
  reflexivity.
Qed.

Lemma classical_Iquest `{Signature} :
  forall phi,
    classical <{? phi}> = false.
Proof.
  intros phi.
  unfold Iquest.
  rewrite classical_Idisj.
  reflexivity.
Qed.

Example iquest_p_not_classical `{Signature} :
  forall p args,
    classical (iquest_p p args) = false.
Proof.
  reflexivity.
Qed.

Example EM_classical `{Signature} :
  forall phi,
    classical (EM phi) = classical phi.
Proof.
  intros phi.
  unfold EM.
  rewrite classical_Disj.
  rewrite classical_Neg.
  rewrite andb_diag.
  reflexivity.
Qed.

Example DNE_classical `{Signature} :
  forall phi,
    classical (DNE phi) = classical phi.
Proof.
  intros phi.
  unfold DNE.
  rewrite classical_Impl.
  do 2 rewrite classical_Neg.
  rewrite andb_diag.
  reflexivity.
Qed.

Lemma classical_hsubst `{Signature} :
  forall phi sigma,
    classical (phi.|[sigma]) = classical phi.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros sigma.
  all: simpl.
  all: try rewrite IH1.
  all: try rewrite IH2.
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

(** ** Free Variables

   For later purposes, we need a predicate to indicate the
   highest occuring free variable in a formula. For this, we
   use substitutions as characteristic property.
 *)

Definition highest_occ_free_var `{Signature}
  (phi : form)
  (x : var) :
  Prop :=

  forall sigma1 sigma2,
    (forall y, y <= x -> sigma1 y = sigma2 y) ->
    phi.|[sigma1] = phi.|[sigma2].
