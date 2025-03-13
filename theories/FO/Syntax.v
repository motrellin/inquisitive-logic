From InqLog Require Export ListLib.
From InqLog.FO Require Export Signatures.

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

   For the helper definition [term_eq_Func_Func_EqDec], the
   recursion principle [eq_rect] on [eq] is used. As [f1] and
   [f2] are equal (with respect to [eq]), we can "translate"
   the type of [args1] from [FAri f1 -> term] to
   [FAri f2 -> term]. This can be done using [eq_rect]:
 *)
Check eq_rect.

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

(**
   With this, the main definition [term_eq] can be defined
   straightforward.
 *)
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

(**
   [term_eq] is indeed an equivalence relation.
 *)
Instance term_eq_Equiv `{Signature} : Equivalence term_eq.
Proof with (try (now firstorder) + congruence + exact FSymb_EqDec).
  constructor.
  -
    intros t.
    induction t as [x|f args IH]...
    (**
       Note, that some simple proofs are solved
       automatically, e.g. the case [t = Var x].

       This will be done more often in the following proofs.
     *)

    simpl.
    destruct (f == f)...
    (**
       Here, it comes in play, that we enforced [FSymb] to
       have decidable equality ([FSymb_EqDec]). Otherwise,
       Axiom K must be stated.
     *)
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

(**
   [term_eq] is indeed decidable, so we state that [term] has
   a decidable equality.
 *)
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

(**
   It is worth to check, whether [rename] respects our
   equality on terms.
*)
Instance rename_Proper `{Signature} :
  Proper (ext_eq ==> term_eq ==> term_eq) rename.
Proof.
  intros sigma1 sigma2 H1 t1.
  generalize dependent sigma2.
  revert sigma1.
  induction t1 as [x1|f1 args1 IH].
  all: intros * H1 [x2|f2 args2] H2.
  all: try contradiction.
  -
    simpl in *.
    subst x2.
    apply H1.
  -
    simpl in *.
    destruct (f1 == f2) as [H3|H3]; try contradiction.
    simpl in H3.
    subst f2.
    simpl in *.
    intros arg.
    apply IH.
    +
      exact H1.
    +
      apply H2.
Qed.

Print Assumptions rename.

Instance Subst_term `{Signature} : Subst term.
Proof. derive. Defined.

(**
   It is worth to check, whether [subst] respects our
   equality on terms.
*)
Instance subst_Proper `{Signature} :
  Proper (ext_eq ==> term_eq ==> term_eq) subst.
Proof.
  intros sigma1 sigma2 H1 t1.
  generalize dependent sigma2.
  revert sigma1.
  induction t1 as [x1|f1 args1 IH].
  all: intros sigma1 sigma2 H1 [x2|f2 args2] H2.
  all: try contradiction.
  -
    simpl in *.
    subst x2.
    apply H1.
  -
    simpl in *.
    destruct (f1 == f2) as [H3|H3]; try contradiction.
    simpl in *.
    subst f2.
    intros arg.
    apply IH.
    +
      apply H1.
    +
      apply H2.
Qed.

Print Assumptions subst_Proper.

Instance up_Proper `{Signature} :
  Proper (ext_eq ==> ext_eq) up.
Proof.
  intros sigma1 sigma2 H1 [|x'].
  -
    reflexivity.
  -
    simpl.
    unfold up.
    simpl.
    rewrite (H1 x').
    reflexivity.
Qed.

Print Assumptions up_Proper.

Instance SubstLemmas_term `{Signature} : SubstLemmas term.
Proof. derive. Qed.

Lemma rename_subst' `{Signature} :
  forall sigma t,
    rename sigma t == t.[ren sigma].
Proof.
  induction t as [x|f args IH].
  -
    reflexivity.
  -
    simpl.
    destruct (f == f) as [H1|H1].
    +
      red.
      rewrite <- eq_rect_eq_dec; try exact FSymb_EqDec.
      exact IH.
    +
      apply H1.
      reflexivity.
Qed.

Lemma subst_id' `{Signature} :
  forall t,
    t.[ids] == t.
Proof.
  induction t as [x|f args IH].
  -
    simpl.
    reflexivity.
  -
    simpl.
    destruct (f == f) as [H1|H1].
    +
      red.
      rewrite <- eq_rect_eq_dec; try exact FSymb_EqDec.
      exact IH.
    +
      apply H1.
      reflexivity.
Qed.

Lemma id_subst' `{Signature} :
  forall sigma x,
    (ids x).[sigma] == sigma x.
Proof.
  reflexivity.
Qed.

Lemma subst_comp' `{Signature} :
  forall sigma1 sigma2 t,
    t.[sigma1].[sigma2] == t.[sigma1 >> sigma2].
Proof.
  induction t as [x|f args IH].
  -
    reflexivity.
  -
    simpl.
    destruct (f == f) as [H1|H1].
    +
      red.
      rewrite <- eq_rect_eq_dec; try exact FSymb_EqDec.
      exact IH.
    +
      apply H1.
      reflexivity.
Qed.

Print Assumptions subst_comp'.

Local Fixpoint repeater {A} (op : A -> A) (n : nat) : A -> A :=
  match n with
  | 0 => id
  | S n' => fun a => op (repeater op n' a)
  end.

Local Lemma repeater_up_ids `{Signature} :
  forall n,
    ext_eq (repeater up n ids) ids.
Proof.
  induction n as [|n' IH].
  -
    reflexivity.
  -
    simpl repeater.
    rewrite IH.
    intros [|x']; reflexivity.
Qed.

Print Assumptions repeater_up_ids.

Lemma scomp_up `{Signature} :
  forall sigma1 sigma2,
    (up sigma1) >> (up sigma2) ==
    up (sigma1 >> sigma2).
Proof.
  intros * [|x'].
  -
    reflexivity.
  -
    intros *.
    simpl scomp.
    unfold up at 3.
    unfold up at 2.
    simpl.
    repeat rewrite rename_subst'.
    repeat rewrite subst_comp'.
    apply subst_Proper.
    +
      intros x.
      apply rename_subst'.
    +
      reflexivity.
Qed.

(** ** Rigidity

   Next, we extend the definition of rigidity to terms.
 *)
Fixpoint term_rigid `{Signature} (t : term) : Prop :=
  match t with
  | Var x => True
  | Func f args =>
      rigid f = true /\
      forall arg,
        term_rigid (args arg)
  end.

Instance term_rigid_Proper `{Signature} :
  Proper (term_eq ==> iff) term_rigid.
Proof.
  intros t1.
  induction t1 as [x1|f1 args1 IH].
  all: intros [x2|f2 args2] H1.
  all: try contradiction.
  -
    reflexivity.
  -
    simpl in H1.
    destruct (f1 == f2) as [H2|H2]; try contradiction.
    simpl in *.
    subst f2.
    split.
    all: intros [H3 H4].
    all: split.
    all: try exact H3.
    all: intros arg.
    all: eapply IH; try exact (H4 arg).
    all: apply H1.
Qed.

Lemma term_rigid_subst `{Signature} :
  forall t (sigma : var -> term),
  (forall x, term_rigid (sigma x)) ->
    term_rigid t ->
    term_rigid t.[sigma].
Proof.
  induction t as [x|f args IH].
  -
    autosubst.
  -
    intros sigma H1 [H2 H3].
    split; eauto.
Qed.

Print Assumptions term_rigid_subst.

Lemma unnamed_helper_Syntax_3 `{Signature} :
  forall sigma,
    (forall x, term_rigid (sigma x)) ->
    forall x,
      term_rigid (up sigma x).
Proof.
  intros sigma H1 x.
  destruct x as [|x'].
  -
    exact I.
  -
    assert (H2 : up sigma (S x') == (sigma x').[ren (+1)])
    by apply rename_subst'.
    rewrite H2.
    apply term_rigid_subst.
    all: easy.
Qed.

(** * Formulas
   Next step is to recursively define _formulas_ over a
   signature. A [form]ula is either
   - an application of a predicate symbol [p] to some terms,
     respecting [PAri p], which is done via a function
     [PAri p -> term],
   - Falsum, which is represented by [Bot],
   - an _Implication_, Conjunction or Inquisivite Disjunction,
   - an universal quantified formula or
   - an inquisivite existential quantified formula.

   Note, that binding is realised by De Bruijn indices,
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

(** ** Decidable Equality

   We follow the same way as we did for [term_eq].
 *)

Definition form_eq_Pred_Pred_EqDec
  `{Signature}
  (rec : relation term)
  (p1 : PSymb)
  (args1 : PAri p1 -> term)
  (p2 : PSymb)
  (args2 : PAri p2 -> term)
  (is_equal : (p1 == p2)%type) : Prop :=

  eq_rect
  p1
  (fun p => (PAri p -> term) -> Prop)
  (fun args =>
    forall arg,
      rec (args1 arg) (args arg)
  )
  p2
  is_equal
  args2.

Fixpoint form_eq `{Signature} (f : form) : form -> Prop :=
  match f with
  | Pred p1 args1 =>
      fun f2 =>
      match f2 with
      | Pred p2 args2 =>
          match equiv_dec p1 p2 with
          | left is_equal =>
              form_eq_Pred_Pred_EqDec term_eq p1 args1 p2 args2 is_equal
          | _ => False
          end
      | _ => False
      end
  | Bot _ =>
      fun f2 =>
      match f2 with
      | Bot _ => True
      | _ => False
      end
  | Impl f11 f12 =>
      fun f2 =>
      match f2 with
      | Impl f21 f22 =>
          form_eq f11 f21 /\ form_eq f12 f22
      | _ => False
      end
  | Conj f11 f12 =>
      fun f2 =>
      match f2 with
      | Conj f21 f22 =>
          form_eq f11 f21 /\ form_eq f12 f22
      | _ => False
      end
  | Idisj f11 f12 =>
      fun f2 =>
      match f2 with
      | Idisj f21 f22 =>
          form_eq f11 f21 /\ form_eq f12 f22
      | _ => False
      end
  | Forall f11 =>
      fun f2 =>
      match f2 with
      | Forall f21 =>
          form_eq f11 f21
      | _ => False
      end
  | Iexists f11 =>
      fun f2 =>
      match f2 with
      | Iexists f21 =>
          form_eq f11 f21
      | _ => False
      end
  end.

Instance form_eq_Equiv `{Signature} : Equivalence form_eq.
Proof with (try (now firstorder) + congruence + exact PSymb_EqDec).
  constructor.
  -
    intros f.
    induction f as [p args| | | | | |]...

    simpl.
    destruct (p == p)...
    rewrite UIP_dec with (p2 := eq_refl)...

    simpl.
    reflexivity.
  -
    intros f1.
    induction f1 as [p1 args1| | | | | |].
    all: intros [p2 args2| | | | | |] H1...

    simpl in *.
    destruct (p1 == p2), (p2 == p1)...
    simpl in *.
    subst.
    rewrite UIP_dec with (p2 := eq_refl)...

    simpl.
    symmetry.
    apply H1.
  -
    intros f1.
    induction f1 as [p1 args1| | | | | |].
    all: intros [p2 args2| | | | | |] [p3 args3| | | | | |] H1 H2...

    simpl in *.
    destruct (p1 == p2), (p2 == p3), (p1 == p3)...
    simpl in *.
    subst.
    rewrite UIP_dec with (p2 := eq_refl)...

    simpl.
    etransitivity; eauto.
Qed.

Print Assumptions term_eq_Equiv.

Program Instance form_Setoid `{Signature} : Setoid form.

Instance form_EqDec `{Signature} : EqDec form_Setoid.
Proof with (try (right; easy) + now firstorder).
  intros f1.
  induction f1 as [p1 args1| | | | | |].
  all: intros [p2 args2| | | | | |]...

  unfold complement in *.
  simpl.
  destruct (p1 == p2)...
  simpl in *.
  subst p2.
  apply finite_choice with (xs := PAri_enum p1).
  all: intro.
  all: apply PAri_enum_charac + apply term_EqDec.
Qed.

Print Assumptions form_EqDec.

(** ** Notation
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

(** ** Substitutions

   And again, we need to derive some [Autosubst]-[Instance]s.
 *)

Instance HSubst_form `{Signature} : HSubst term form.
Proof. derive. Defined.

Instance hsubst_Proper `{Signature} :
  Proper (ext_eq ==> form_eq ==> form_eq) hsubst.
Proof.
  intros sigma1 sigma2 H1 f1.
  generalize dependent sigma2.
  revert sigma1.
  induction f1 as
  [p1 args1
  |?
  |f11 IH1 f12 IH2
  |f11 IH1 f12 IH2
  |f11 IH1 f12 IH2
  |f11 IH1
  |f11 IH1].
  all: intros sigma1 sigma2 H1
  [p2 args2
  |?
  |f21 f22
  |f21 f22
  |f21 f22
  |f21
  |f21].
  all: intros H2; try (now firstorder).
  -
    simpl in *.
    destruct (p1 == p2) as [H3|H3]; try contradiction.
    simpl in H3.
    subst p2.
    simpl in *.
    intros arg.
    apply subst_Proper.
    +
      exact H1.
    +
      apply H2.
  -
    simpl in *.
    apply IH1.
    +
      intros [|x'].
      *
        reflexivity.
      *
        unfold up.
        simpl.
        do 2 rewrite rename_subst'.
        red in H1.
        rewrite H1.
        reflexivity.
    +
      exact H2.
  -
    simpl in *.
    apply IH1.
    +
      intros [|x'].
      *
        reflexivity.
      *
        unfold up.
        simpl.
        do 2 rewrite rename_subst'.
        red in H1.
        rewrite H1.
        reflexivity.
    +
      exact H2.
Qed.

Print Assumptions hsubst_Proper.

Instance Ids_form `{Signature} : Ids form.
Proof. derive. Defined.

Instance Rename_form `{Signature} : Rename form.
Proof. derive. Defined.

Instance Subst_form `{Signature} : Subst form.
Proof. derive. Defined.

Instance HSubstLemmas_form `{Signature} : HSubstLemmas term form.
Proof. derive. Qed.

(**
   We provide lemmas similar lemmas for our defined
   equality [form_eq].
 *)
Lemma hsubst_id' `{Signature} :
  forall phi,
    phi.|[ids] == phi.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: try now firstorder.
  -
    simpl.
    destruct (p == p) as [H1|H1].
    +
      red.
      rewrite <- eq_rect_eq_dec; try exact PSymb_EqDec.
      intros arg.
      apply subst_id'.
    +
      apply H1.
      reflexivity.
  -
    simpl.
    rewrite <- IH1 at 2.
    apply hsubst_Proper.
    +
      exact (repeater_up_ids 1).
    +
      reflexivity.
  -
    simpl.
    rewrite <- IH1 at 2.
    apply hsubst_Proper.
    +
      exact (repeater_up_ids 1).
    +
      reflexivity.
Qed.

Print Assumptions hsubst_id'.

Lemma id_hsubst' `{Signature} :
  forall sigma x,
    (ids x).|[sigma] == ids x.
Proof.
  reflexivity.
Qed.

Print Assumptions id_hsubst'.

Lemma hsubst_comp' `{Signature} :
  forall sigma1 sigma2 phi,
    phi.|[sigma1].|[sigma2] == phi.|[sigma1 >> sigma2].
Proof.
  intros sigma1 sigma2 phi.
  revert sigma1 sigma2.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros sigma1 sigma2.
  all: try now firstorder.
  -
    simpl.
    destruct (p == p) as [H1|H1].
    +
      red.
      rewrite <- eq_rect_eq_dec; try exact PSymb_EqDec.
      intros arg.
      apply subst_comp'.
    +
      apply H1.
      reflexivity.
  -
    simpl.
    rewrite IH1.
    apply hsubst_Proper; try reflexivity.
    apply scomp_up.
  -
    simpl.
    rewrite IH1.
    apply hsubst_Proper; try reflexivity.
    apply scomp_up.
Qed.

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

Example Kuroda `{Signature} (phi : form) : form :=
  <{(forall (~ ~ phi)) -> ~ ~ forall phi}>.

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
  apply andb_true_r.
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
  apply andb_diag.
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
  apply andb_diag.
Qed.

Example DNE_classical `{Signature} :
  forall phi,
    classical (DNE phi) = classical phi.
Proof.
  intros phi.
  unfold DNE.
  rewrite classical_Impl.
  do 2 rewrite classical_Neg.
  apply andb_diag.
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

Print Assumptions classical_variant_is_classical.

(** ** Free Variables

   For later purposes, we need a predicate to indicate the
   highest occuring free variable in a formula. For this, we
   use substitutions as characteristic property.

   Is is worth to note that standard [eq]uality is used here
   which is of course stronger than [form_eq].
 *)

Definition highest_occ_free_var `{Signature}
  (phi : form)
  (ox : option var) :
  Prop :=

  forall sigma1 sigma2,
    (
      forall y,
        match ox with
        | Some x => y <= x
        | None => True
        end ->
        sigma1 y == sigma2 y
    ) ->
    phi.|[sigma1] == phi.|[sigma2].

(** * Syntax for the Unary Predicate Symbol Signature *)

Module Syntax_single_unary_predicate.

  Export Signature_single_unary_predicate.

  (**
     First, we introduce some nice notation for the unary
     predicate symbol and show certain properties about it.
   *)
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

End Syntax_single_unary_predicate.

(** * Syntax for the Binary Predicate Symbol Signature *)

Module Syntax_single_binary_predicate.

  Export Signature_single_binary_predicate.

  (**
     Same procedure for this signature.
   *)
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

End Syntax_single_binary_predicate.
