From InqLog.FO Require Export Consequence Seq.

(** * The Casari Scheme *)

Definition CasariSuc `{Signature} (phi : form) : form :=
  <{ forall phi }>.

Definition CasariImpl `{Signature} (phi : form) : form :=
  Impl phi (CasariSuc phi).

Definition CasariAnt `{Signature} (phi : form) : form :=
  <{ forall CasariImpl phi -> CasariSuc phi }>.

Definition Casari `{Signature} (phi : form) : form :=
  <{ CasariAnt phi -> CasariSuc phi }>.

Remark Casari_truth_conditional `{Signature} :
  forall phi,
    classical phi = true ->
    truth_conditional (Casari phi).
Proof.
  intros phi H1.
  apply classical_truth_conditional.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

(** * Some Casari Instances with atomic predicates *)

Module Casari_with_atoms.

  Import Syntax_single_unary_predicate.

  Definition Atomic : form :=
    <{ Pred' (Var 0) }>.

  Definition DNA : form :=
    <{ ~ ~ (Pred' (Var 0)) }>.

  Remark Casari_DNA_Prop (P : var -> Prop) :
    (
      forall x,
        (
          (P x)
          ->
          (forall x, ~ ~ P x)
        )
        ->
        (forall x, ~ ~ P x)
    )
    ->
    (
      forall x, ~ ~ P x
    ).
  Proof.
    firstorder.
  Qed.

  Theorem support_valid_Casari_DNA :
    support_valid (Casari DNA).
  Proof.
    apply support_valid_charac_support_conseq.
    apply support_conseq_Impl_I.
    apply support_conseq_Forall_I.
    apply support_conseq_Impl_I.
    apply support_conseq_Bot_I with
      (phi := <{~ (Pred' (Var 0))}>).
    -
      apply support_conseq_weakening_cons_hd.
    -
      assert (eq1 :
        <{~ ~ (Pred' (Var 0))}> =
        <{~ ~ (Pred' (Var 0))}>.|[Var 0/]
      ). reflexivity.
      rewrite eq1.
      apply support_conseq_Forall_E_rigid; try easy.
      apply support_conseq_Impl_E with
        (phi := CasariImpl DNA).
      +
        apply support_conseq_Impl_I.
        apply support_conseq_Bot_E.
        apply support_conseq_Bot_I with
          (phi := <{~ Pred' (Var 0)}>).
        *
          apply support_conseq_weakening_cons_tl.
          apply support_conseq_weakening_cons_hd.
        *
          apply support_conseq_weakening_cons_hd.
      +
        assert (eq2 :
          <{ (CasariImpl DNA) -> (Forall <{ ~ ~ (Pred' (Var 0)) }>) }> =
          <{ (CasariImpl DNA) -> (Forall <{ ~ ~ (Pred' (Var 0)) }>) }>.|[Var 0/]
        ). reflexivity.
        rewrite eq2.
        apply support_conseq_Forall_E_rigid; try easy.
        apply support_conseq_weakening_cons_tl.
        apply support_conseq_weakening_cons_hd.
  Qed.

  Proposition support_conseq_CasariSuc_DNA_CasariSuc_Atomic :
    support_conseq (CasariSuc DNA :: nil) (CasariSuc Atomic).
  Proof.
    apply support_conseq_Forall_I.
    eapply support_conseq_Impl_E with
      (phi := DNA).
    -
      apply support_conseq_Impl_I.
      apply support_conseq_Bot_I with
        (phi := <{~ Pred' (Var 0)}>).
      +
        apply support_conseq_weakening_cons_hd.
      +
        apply support_conseq_weakening_cons_tl.
        apply support_conseq_Impl_I.
        eapply support_conseq_Impl_E.
        *
          apply support_conseq_weakening_cons_hd.
        *
          apply support_conseq_weakening_cons_tl.
          unfold CasariSuc.
          unfold DNA.
          assert (eq1 :
            <{~ (Pred' (Var 0)) -> (Bot 0)}> =
            <{~ (Pred' (Var 0)) -> (Bot 0)}>.|[Var 0/]
          ). reflexivity.
          rewrite eq1.
          apply support_conseq_Forall_E_rigid; try exact I.
          apply support_conseq_refl.
    -
      rewrite <- app_nil_l with
        (l := map (fun psi => psi.|[ren (+1)]) (CasariSuc DNA :: nil)).
      eapply support_conseq_weakening_1.
      apply support_valid_charac_support_conseq.
      apply support_valid_DNE_Pred.
  Qed.

  Print Assumptions support_conseq_CasariSuc_DNA_CasariSuc_Atomic.

  Proposition support_conseq_CasariSuc_Atomic_CasariSuc_DNA :
    support_conseq (CasariSuc Atomic :: nil) (CasariSuc DNA).
  Proof.
    apply support_conseq_Forall_I.
    apply support_conseq_Impl_I.
    apply support_conseq_Bot_I with
      (phi := Pred' (Var 0)).
    -
      apply support_conseq_weakening_cons_tl.
      assert (eq1 :
        Pred' (Var 0) = (Pred' (Var 0)).|[Var 0/]
      ). reflexivity.
      rewrite eq1.
      apply support_conseq_Forall_E_rigid; try exact I.
      apply support_conseq_refl.
    -
      apply support_conseq_weakening_cons_hd.
  Qed.

  Print Assumptions support_conseq_CasariSuc_Atomic_CasariSuc_DNA.

  Proposition support_conseq_CasariAnt_Atomic_CasariAnt_DNA :
    support_conseq (CasariAnt Atomic :: nil) (CasariAnt DNA).
  Proof.
    apply support_conseq_Forall_I.
    apply support_conseq_Impl_I.
    apply support_conseq_trans with
      (cxt2 := CasariSuc Atomic :: nil).
    -
      intros psi [H3|H3]; try easy.
      subst psi.
      apply support_conseq_Impl_E with
        (phi := CasariImpl Atomic).
      +
        apply support_conseq_Impl_I.
        apply support_conseq_trans with
          (cxt2 := CasariSuc DNA :: nil).
        *
          intros psi [H3|H3]; try easy.
          subst psi.
          apply support_conseq_Impl_E with
            (phi := DNA).
          --
             apply support_conseq_Impl_I.
             apply support_conseq_Bot_I with (phi := Atomic).
             ++
                apply support_conseq_weakening_cons_tl.
                apply support_conseq_weakening_cons_hd.
             ++
                apply support_conseq_weakening_cons_hd.
          --
             apply support_conseq_in.
             right.
             left.
             reflexivity.
        *
          exact support_conseq_CasariSuc_DNA_CasariSuc_Atomic.
      +
        assert (eq1 :
          <{ (CasariImpl Atomic) -> (CasariSuc Atomic) }> =
          <{ (CasariImpl Atomic) -> (CasariSuc Atomic) }>.|[Var 0/]
        ). reflexivity.
        rewrite eq1.
        apply support_conseq_Forall_E_rigid; try exact I.
        apply support_conseq_in.
        right.
        left.
        reflexivity.
    -
      exact support_conseq_CasariSuc_Atomic_CasariSuc_DNA.
  Qed.

  Print Assumptions support_conseq_CasariAnt_Atomic_CasariAnt_DNA.

  Proposition support_conseq_Casari_DNA_Casari_Atomic :
    support_conseq (Casari DNA :: nil) (Casari Atomic).
  Proof.
    apply support_conseq_Impl_I.
    apply support_conseq_trans with
      (cxt2 := CasariSuc DNA :: nil).
    -
      intros psi [H4|H4]; try easy.
      subst psi.
      apply support_conseq_Impl_E with
        (phi := CasariAnt DNA).
      +
        apply support_conseq_trans with
          (cxt2 := CasariAnt Atomic :: nil).
        *
          intros psi [H4|H4]; try easy.
          subst psi.
          apply support_conseq_weakening_cons_hd.
        *
          exact support_conseq_CasariAnt_Atomic_CasariAnt_DNA.
      +
        apply support_conseq_in.
        right.
        left.
        reflexivity.
    -
      exact support_conseq_CasariSuc_DNA_CasariSuc_Atomic.
  Qed.

  Print Assumptions support_conseq_Casari_DNA_Casari_Atomic.

  Corollary support_valid_Casari_Atomic :
    support_valid (Casari Atomic).
  Proof.
    apply support_valid_charac_support_conseq.
    apply support_conseq_trans with
      (cxt2 := Casari DNA :: nil).
    -
      intros psi [H1|H1]; try easy.
      subst psi.
      apply support_valid_charac_support_conseq.
      exact support_valid_Casari_DNA.
    -
      exact support_conseq_Casari_DNA_Casari_Atomic.
  Qed.

  Print Assumptions support_valid_Casari_Atomic.

End Casari_with_atoms.

(** * The Casari "counter-example"

   We will now provide a counter-example to show that the
   Casari Scheme isn't schematically valid. For this, we
   need a concrete signature, a concret instance of the
   scheme via a formula [phi], a suitable model [M], a state
   [s] and a variable assignment [a] s.t. [M], [s] and [a]
   do not support [phi].
 *)
Module Casari_fails.

  Import PeanoNat.Nat.

  Local Arguments contains _ _ s w /.

  (** ** Signature and Syntax

     We will use our signature with a single binary
     predicate symbol for the counter example.
   *)
  Import Syntax_single_binary_predicate.

  (**
     The following formula will serve as our instance for
     the Casari Scheme:
   *)
  Definition IES : form :=
    <{iexists (Pred' (Var 1) (Var 0))}>.

  (**
     We can verify that [IES] has only one free variable.
   *)
  Remark highest_occ_free_var_IES :
    highest_occ_free_var IES (Some 0).
  Proof.
    intros sigma1 sigma2 H1.
    simpl.
    red.
    rewrite <- eq_rect_eq_dec; try exact PSymb_EqDec.
    intros [|]; try reflexivity.
    unfold mmap.
    unfold MMap_fun.
    unfold up.
    simpl.
    do 2 rewrite rename_subst'.
    rewrite H1; reflexivity.
  Qed.

  Print Assumptions highest_occ_free_var_IES.

  (** ** The Model

     For our model, we decide on natural numbers to serve as
     our type of Worlds and Individuals. By this,
     [PInterpretation] becomes a ternary relation which we
     define before:
   *)
  Definition rel (w m j : nat) : bool :=
    (
      negb (even m) &&
      (m =? j)
    ) ||
    (
      even m &&
      negb (j =? w) &&
      (
        negb (even j) ||
        (m <? j)
      )
    ).

  (**
     We will now instantiate the model.
   *)

  Local Obligation Tactic :=
    try decide equality;
    try contradiction.

  Program Instance M : Model :=
    {|
      World := nat;
      World_Setoid := eq_setoid nat;
      Individual := nat;
      Individual_inh := 42;
      PInterpretation :=
        fun w p args =>
        rel w (args true) (args false)
    |}.

  Next Obligation.
    intros w p args1 args2 H1.
    repeat rewrite H1.
    reflexivity.
  Qed.

  Next Obligation.
    intros w1 w2 H1.
    reflexivity.
  Qed.

  (** ** Intermezzo: Some classical logic properties *)

  Lemma not_exists_forall_not {X} :
    forall (P : X -> Prop),
      ~ (exists x, P x) ->
      forall x,
        ~ P x.
  Proof.
    firstorder.
  Qed.

  Lemma not_forall_exists_not {X} :
    forall (P : X -> Prop),
      ~ (forall x, P x) ->
      exists x,
        ~ P x.
  Proof.
    intros P H1.
    apply NNPP.
    intros H2.
    apply H1.
    intros x.
    eapply not_exists_forall_not in H2.
    apply NNPP.
    exact H2.
  Qed.

  (** ** Some state properties

     We start by defining some notation for state
     properties.
   *)

  Declare Custom Entry boolpred.

  Notation "(? p ?)" := p
    (at level 0,
    p custom boolpred at level 99)
    : form_scope.

  Notation "( x )" := x
    (in custom boolpred, x at level 99)
    : form_scope.

  Notation "x" := x
    (in custom boolpred at level 0, x constr at level 0)
    : form_scope.

  Notation "f x .. y" := (.. (f x) .. y)
    (in custom boolpred at level 0,
    only parsing,
    f constr at level 0,
    x constr at level 9,
    y constr at level 9)
    : form_scope.

  Notation "p1 && p2" := (fun w => p1 w && p2 w)
    (in custom boolpred at level 40, right associativity)
    : form_scope.

  Notation "p1 || p2" := (fun w => p1 w || p2 w)
    (in custom boolpred at level 50, right associativity)
    : form_scope.

  Notation "~ p" := (fun w => negb (p w))
    (in custom boolpred at level 75)
    : form_scope.

  (**
     We define [contains_all p] to say that s contains all
     worlds with property [p]. Note that this is in fact a
     duplicate of [substate] which is intended to
     distinguish between properties of worlds and states.
   *)

  Definition contains_all (p : nat -> bool) (s : state) : Prop :=
    forall w,
      p w = true ->
      contains s w.

  Instance contains_all_Proper :
    forall p,
      Proper (state_eq ==> iff) (contains_all p).
  Proof.
    intros p s1 s2 H1.
    split.
    -
      intros H2 w H3.
      rewrite <- H1.
      apply H2.
      exact H3.
    -
      intros H2 w H3.
      rewrite H1.
      apply H2.
      exact H3.
  Qed.

  Lemma substate_contains_all :
    forall p s t,
      substate t s ->
      contains_all p t ->
      contains_all p s.
  Proof.
    intros p s t H1 H2 w H3.
    apply H1.
    apply H2.
    exact H3.
  Qed.

  (**
     Next, we implement the notion that a state contains at
     least one world with property [p].
   *)
  Definition contains_any (p : nat -> bool) (s : state) : Prop :=
    exists w,
      p w = true /\
      contains s w.

  Instance contains_any_Proper :
    forall p,
      Proper (state_eq ==> iff) (contains_any p).
  Proof.
    intros p s1 s2 H1.
    split.
    -
      intros [w [H2 H3]].
      exists w.
      rewrite <- H1.
      split; assumption.
    -
      intros [w [H2 H3]].
      exists w.
      rewrite H1.
      split; assumption.
  Qed.

  Instance contains_any_Proper_substate :
    Proper (ext_eq ==> substate ==> impl) contains_any.
  Proof.
    intros p1 p2 H1 t s H2 [w [H3 H4]].
    exists w.
    split.
    -
      rewrite <- H1.
      exact H3.
    -
      rewrite <-H2.
      exact H4.
  Qed.

  Lemma not_contains_any_contains_all_complement :
    forall p s,
      ~ contains_any p s ->
      contains_all p (States.complement s).
  Proof.
    intros p s H1 w H2.
    apply contains_complement_iff.
    unfold contains_any in H1.
    apply not_exists_forall_not with (x := w) in H1.
    destruct (p w), (s w).
    all: firstorder.
  Qed.

  (**
     We also define the property to have at most finitely
     many worlds with property [p]. We do this by stating
     that there exists a maximal world with property [p].
   *)

  Definition is_border
    (p : nat -> bool)
    (s : state)
    (e : nat) : Prop :=

    forall w,
      p w = true ->
      contains s w ->
      w <=? e = true.

  Definition finitely_many (p : nat -> bool) (s : state) : Prop :=
    exists e,
      is_border p s e.

  Instance finitely_many_Proper :
    forall p,
      Proper (state_eq ==> iff) (finitely_many p).
  Proof.
    intros p s1 s2 H1.
    unfold finitely_many.
    split.
    all: intros [e H2].
    all: exists e.
    all: intros w H3 H4.
    all: specialize (H2 w).
    -
      rewrite <- H1 in H4.
      auto.
    -
      rewrite H1 in H4.
      auto.
  Qed.

  Lemma substate_finitely_many :
    forall p s t,
      substate t s ->
      finitely_many p s ->
      finitely_many p t.
  Proof.
    intros p s t H1 [e H2].
    exists e.
    intros w H3 H4.
    apply H2.
    -
      exact H3.
    -
      apply H1.
      exact H4.
  Qed.

  (**
     We also implement the converse notion of having
     infinitely many worlds with property [p].
   *)

  Definition successor
    (p : nat -> bool)
    (s : state)
    (w e : nat) : Prop :=

    p e = true /\
    contains s e /\
    w <? e = true.

  Instance successor_Proper :
    Proper (ext_eq ==> state_eq ==> Logic.eq ==> Logic.eq ==> iff)
    successor.
  Proof.
    intros p1 p2 H1 s1 s2 H2 w1 w2 H3 e1 e2 H4.
    simpl in *.
    subst w2 e2.
    unfold successor.
    rewrite H1,H2.
    reflexivity.
  Qed.

  Definition infinitely_many (p : nat -> bool) (s : state) : Prop :=
    forall w,
      exists e,
        successor p s w e.

  Instance infinitely_many_Proper :
    Proper (ext_eq ==> state_eq ==> iff) infinitely_many.
  Proof.
    intros p1 p2 H1 s1 s2 H2.
    unfold infinitely_many.
    split.
    all: intros H3 w.
    all: specialize (H3 w) as [e H3].
    all: exists e.
    all: rewrite H1,H2 in *.
    all: easy.
  Qed.

  (**
     It is worth to note that we need classic logic to show
     the we conclude finiteness from missing infiniteness
     and infiniteness from missing finiteness.
   *)

  Lemma not_infinitely_many_finitely_many :
    forall p s,
      ~ infinitely_many p s ->
      finitely_many p s.
  Proof.
    intros p s H1.
    apply not_forall_exists_not in H1 as [n H1].
    exists n.
    intros w H2 H3.
    apply not_exists_forall_not with (x := w) in H1.
    unfold successor in H1.
    rewrite ltb_lt in H1.
    rewrite leb_le.
    unfold contains in *.
    destruct (p w), (s w).
    all: lia.
  Qed.

  Instance infinitely_many_Proper_substate :
    Proper (ext_eq ==> substate ==> impl) infinitely_many.
  Proof.
    intros p1 p2 H1 t s H2 H3 n.
    destruct (H3 n) as [e [H4 [H5 H6]]].
    exists e.
    red.
    rewrite H1 in H4.
    eauto using substate_contrapos.
  Qed.

  (**
     Last, we define a state property which will be needed
     later.
   *)
  Local Definition E (s : state) : Prop :=
    contains_any (? ~ even ?) (States.complement s) \/
    infinitely_many even (States.complement s).

  Instance E_Proper_substate :
    Proper (substate --> impl) E.
  Proof.
    intros s t H1 [H2|H2].
    -
      left.
      rewrite <- H1.
      exact H2.
    -
      right.
      rewrite <- H1.
      exact H2.
  Qed.

  Lemma not_E_contains_all :
    forall s,
      ~ E s ->
      contains_all (? ~ even ?) s.
  Proof.
    intros * H1.
    apply Decidable.not_or in H1 as [H1 _].
    apply not_contains_any_contains_all_complement in H1.
    rewrite complement_involutive in H1.
    exact H1.
  Qed.

  Lemma not_E_finitely_many_complement :
    forall s,
      ~ E s ->
      finitely_many even (States.complement s).
  Proof.
    intros * H1.
    apply Decidable.not_or in H1 as [_ H1].
    apply not_infinitely_many_finitely_many in H1.
    exact H1.
  Qed.

  (**
     We prove some helper lemmas which do not have any
     meaningful names yet.
   *)

  Lemma unnamed_helper_Casari_1 :
    forall w m,
      even m = true ->
      rel w m w = false.
  Proof.
    intros w m H1.
    unfold rel.
    rewrite H1.
    rewrite eqb_refl.
    reflexivity.
  Qed.

  Print Assumptions unnamed_helper_Casari_1.

  Lemma unnamed_helper_Casari_2 :
    forall (s : state) (m : nat),
      even m = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? ltb m ?) s ->
      forall w j,
        rel w m j = true ->
        contains s j.
  Proof.
    intros s m H1 H2 H3 w j H4.

    unfold rel in H4.
    rewrite H1 in H4.
    simpl in H4.
    destruct (j =? w) eqn:H6; try discriminate.
    simpl in H4.
    apply orb_true_iff in H4 as [H4|H4].
    all: auto.
  Qed.

  Print Assumptions unnamed_helper_Casari_2.

  Local Program Definition unnamed_helper_Casari_3_state
    (n e : nat) : state :=

    {|
      morph :=
        fun w =>
        (S (S (max n e)) <? w) || negb (even w)
    |}.

  Lemma unnamed_helper_Casari_3 :
    forall (s : state) (n : nat),
      contains_all (? ~ even ?) s ->
      finitely_many (? even ?) (States.complement s) ->
      exists t,
        substate t s /\
        contains_all (? ~ even ?) t /\
        finitely_many (? even ?) (States.complement t) /\
        contains_any (? ltb n ?) (States.complement t).
  Proof.
    intros s n H1 [e H2].
    (**
       [e] is the greatest even number not in [s].
       We're looking for a [substate] [t] of [s], s.t.
       there also exists a greatest even number not in [t] and
       with one even number contained greater than [a x].
     *)
    exists (unnamed_helper_Casari_3_state n e).
    repeat split.
    -
      intros w H4.
      simpl in H4.
      destruct (even w) eqn:H3.
      +
        rewrite orb_false_r in H4.
        specialize (H2 _ H3).
        destruct (contains_dec s w) as [H5|H5]; try assumption.
        rewrite contains_complement_iff in H2.
        specialize (H2 H5).
        apply leb_le in H2.
        apply ltb_lt in H4.
        lia.
      +
        apply H1.
        rewrite H3.
        reflexivity.
    -
      intros w H3.
      simpl.
      rewrite H3.
      apply orb_true_r.
    -
      exists (S (S (max n e))).
      intros w H3 H4.
      rewrite contains_complement_iff in H4.
      apply not_true_is_false in H4.
      apply orb_false_iff in H4 as [H4 H5].
      apply ltb_nlt in H4.
      apply leb_le.
      lia.
    -
      exists (
        if even (max n e)
        then S (S (max n e))
        else S (max n e)
      ).
      split.
      +
        destruct (even (max n e)).
        all: apply ltb_lt.
        all: lia.
      +
        rewrite contains_complement_iff.
        apply not_true_iff_false.
        apply orb_false_iff.
        split.
        *
          apply ltb_nlt.
          destruct (even (max n e)).
          all: lia.
        *
          destruct (even (max n e)) eqn:H3.
          --
             simpl.
             rewrite H3.
             reflexivity.
          --
             rewrite negb_even.
             rewrite odd_succ.
             exact H3.
  Qed.

  Print Assumptions unnamed_helper_Casari_3.

  (** ** Support for [IES]

     We start by analysing support for [IES] itself.
   *)

  (**
     [support_IES_odd] represents Claim 3.7. in Litak/Sano
   *)
  Proposition support_IES_odd :
    forall (s : state) (a : assignment),
      even (a 0) = false ->
      s, a |= IES.
  Proof.
    intros s a H1.

    exists (a 0).

    intros w H2.
    simpl.
    unfold rel.

    rewrite H1.
    rewrite eqb_refl.
    reflexivity.
  Qed.

  Print Assumptions support_IES_odd.

  (**
     [support_IES_even] and
     [support_IES_even_other_direction] represent Claim 3.8.
   *)
  Proposition support_IES_even :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      contains_any (? (~ even) || ltb (a 0) ?) (States.complement s) ->
      s, a |= IES.
  Proof.
    intros s a H1 [n [H2 H3]].

    (**
       For preparation, just remove the notion of a
       complement.
     *)
    apply contains_complement_iff in H3.

    simpl.
    (**
       The obvious candidate is n which can be easily
       observed by the definition of [rel].
     *)
    exists n.
    intros w H4.

    unfold rel.
    rewrite H1.
    simpl.
    rewrite andb_true_iff.
    split.
    -
      destruct (n =? w) eqn:H5; try reflexivity.
      apply eqb_eq in H5.
      subst w.
      Fail congruence.
      simpl in H3. (* Why is this needed? *)
      congruence.
    -
      apply orb_true_iff in H2 as [H2|H2].
      +
        rewrite H2.
        reflexivity.
      +
        rewrite H2.
        apply orb_true_r.
  Qed.

  Print Assumptions support_IES_even.

  Proposition support_IES_even_other_direction :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? ltb (a 0) ?) s ->
      ~ (s, a |= IES).
  Proof.
    intros s a H1 H2 H3 [i H4].
    simpl in H4.

    pose proof (unnamed_helper_Casari_1 i _ H1) as H5.
    pose proof (unnamed_helper_Casari_2 _ _ H1 H2 H3) as H6.

    assert (H7 : s i = true).
    {
      apply H6 with (w := 1).
      apply H4.
      apply H2.
      reflexivity.
    }
    specialize (H4 _ H7).
    congruence.
  Qed.

  (** ** Support for [CasariSuc IES]

     We will now prove helpful support properties for
     [CasariSuc IES]. In fact, we get
     [E s <-> s, a |= <{CasariSuc IES}>]. The two directions
     are proven in [support_CasariSuc_IES] and
     [support_CasariSuc_IES_other_direction].
   *)

  Proposition support_CasariSuc_IES :
    forall (s : state) (a : assignment),
      E s ->
      s, a |= <{ CasariSuc IES }>.
  Proof.
    intros s a H1 i.
    (**
       We start by a case distinction whether [i] is [even].
     *)
    destruct (even i) eqn:H2.
    -
      (**
         For the first case, we just destruct the property
         of [s] being a member of [E], as it is a
         disjunctive property.
       *)
      destruct H1 as [[n [H11 H12]]|H1].
      +
        apply support_IES_even.
        *
          exact H2.
        *
          exists n.
          split.
          --
             rewrite H11.
             reflexivity.
          --
             exact H12.
      +
        destruct (H1 i) as [e [H3 [H4 H5]]].
        eapply support_IES_even.
        *
          exact H2.
        *
          exists e.
          simpl in *.
          rewrite H3,H4,H5.
          split; reflexivity.
    -
      eapply support_IES_odd.
      exact H2.
  Qed.

  Print Assumptions support_CasariSuc_IES.

  (**
     For the other direction, we prove a version which can
     be gained by contraposition.
   *)
  Proposition support_CasariSuc_IES_other_direction :
    forall (s : state) (a : assignment) (e : nat),
      contains_all (? ~ even ?) s ->
      contains_all (? ltb e ?) s ->
      ~ (s, a |= <{CasariSuc IES}>).
  Proof.
    intros s a e H1 H2 H3.

    unfold CasariSuc in H3.
    rewrite support_Forall in H3.

    (**
       Note the chosen [a] for applying
       [support_IES_even_other_direction]. By this, [a 0]
       is for sure even.
     *)
    eapply support_IES_even_other_direction with
      (a := (if even e then e else S e) .: a).
    -
      destruct (even e) eqn:H4.
      +
        exact H4.
      +
        remember ((S e .: a) 0) as n eqn:eq1.
        simpl in eq1.
        subst n.

        rewrite even_succ.
        unfold odd.
        rewrite H4.
        reflexivity.
    -
      exact H1.
    -
      intros w H4.
      apply H2.
      apply ltb_lt in H4.
      apply ltb_lt.
      simpl in H4.
      destruct (even e); [exact H4|lia].
    -
      apply H3.
  Qed.

  Print Assumptions support_CasariSuc_IES_other_direction.

  (** ** Support for [CasariImpl IES]

     In this section, we will prove needed support
     properties for [CasariImpl IES]. The main result is
     [support_CasariImpl_IES_other_direction].
   *)

  Proposition support_CasariImpl_IES_other_direction :
    forall (s : state) (a : assignment),
      contains_all (? ~ even ?) s ->
      finitely_many even (States.complement s) ->
      ~ (s, a |= CasariImpl IES).
  Proof.
    intros s a H1 H2 H3.
    pose proof (unnamed_helper_Casari_3 _ (a 0) H1 H2) as
      [t [H5 [H6 [H7 H8]]]].
    destruct H7 as [e1 H7].
    eapply support_CasariSuc_IES_other_direction with
      (e := e1).
    -
      exact H6.
    -
      intros w H9.
      destruct (even w) eqn:HA.
      +
        specialize (H7 _ HA).
        destruct (contains_dec t w) as [HB|HB]; try assumption.
        rewrite contains_complement_iff in H7.
        specialize (H7 HB).
        apply leb_le in H7.
        apply ltb_lt in H9.
        lia.
      +
        apply H6.
        rewrite HA.
        reflexivity.
    -
      unfold CasariImpl in H3.
      rewrite support_Impl in H3.
      apply H3.
      +
        exact H5.
      +
        destruct (even (a 0)) eqn:H9.
        *
          apply support_IES_even.
          --
             exact H9.
          --
             destruct H8 as [e2 [H81 H82]].
             exists e2.
             simpl in *.
             rewrite H81,H82.
             rewrite orb_true_r.
             split; reflexivity.
        *
          apply support_IES_odd.
          exact H9.
  Qed.

  Print Assumptions support_CasariImpl_IES_other_direction.

  (** ** Support for [CasariAnt IES]

     Now, we can stick our previously proved propositions
     together. By this, we get that [CasariAnt IES] is
     valid in our instantiated model [M].

     For this, we use classical logic in two points:
     - In order to apply contraposition via [NNPP] and
     - when we are applying
       [not_E_finitely_many_complement].
   *)
  Proposition support_CasariAnt_IES :
    forall (s : state) (a : assignment),
      s, a |= <{CasariAnt IES}>.
  Proof.
    intros s a i t H1 H2.
    apply support_CasariSuc_IES.

    apply NNPP.
    intros H3.
    eapply support_CasariImpl_IES_other_direction.
    -
      apply not_E_contains_all.
      exact H3.
    -
      apply not_E_finitely_many_complement.
      exact H3.
    -
      exact H2.
  Qed.

  Print Assumptions support_CasariAnt_IES.

  (** ** Support for [Casari IES]

     We now conclude that we have indeed found a suitable
     counter-example. For this, we still need to define a
     suitable state. We would also need a concrete
     [assignment] but this can be done one the fly.

     [counter_state e] is a state that contains every odd
     number and every (even) number greater than [e]. By
     this, it contains at least one odd number and its
     complement can only contain infinitely many even
     numbers.
   *)
  Local Program Definition counter_state (e : nat) : state :=
    {|
      morph :=
        fun w =>
        (e <? w) || negb (even w)
    |}.

  Fact counter_state_contains_all_odds :
    forall e,
      contains_all (? ~ even ?) (counter_state e).
  Proof.
    intros e w H1.
    simpl.
    rewrite H1.
    apply orb_true_r.
  Qed.

  Fact counter_state_contains_all_ltb :
    forall e,
      contains_all (? ltb e ?) (counter_state e).
  Proof.
    intros e w H1.
    simpl.
    rewrite H1.
    reflexivity.
  Qed.

  Theorem not_support_valid_Casari_IES :
    ~ support_valid <{Casari IES}>.
  Proof.
    intros H1.

    (**
       As [Casari IES] is an implication with conclusion
       [CasariSuc IES], we try to falsify this.
     *)
    eapply support_CasariSuc_IES_other_direction.
    -
      apply counter_state_contains_all_odds.
    -
      apply counter_state_contains_all_ltb.
    -
      eapply H1.
      +
        reflexivity.
      +
        fold support.
        apply support_CasariAnt_IES.

    (**
       We still need to instantiate some existential
       variables.
     *)
    Unshelve.
    exact (fun _ => 25). (* any variable [assignment] *)
    exact 24. (* concrete instance of [counter_state] *)
  Qed.

  Print Assumptions not_support_valid_Casari_IES.
  (*
      Axioms:
        classic : forall P : Prop, P \/ ~ P
   *)

End Casari_fails.

(** * Bounded Casari

   We will now prove that the Casari Scheme is valid for
   every formula with the property that the highest occuring
   free variable is at most 0. We will proceed by providing
   a derivation using [Seq] and its [soundness].
 *)

Theorem Seq_CasariAnt_CasariSuc `{Signature} :
  forall ns (phi : form) sigma,
    highest_occ_free_var phi (Some 0) ->
    Seq
    ((pair ns (CasariAnt phi).|[sigma]) :: nil)
    ((pair ns (CasariSuc phi).|[sigma]) :: nil).
Proof.
  (**
     Proof by induction on the size of the label [ns].
   *)
  induction ns as [ns IH] using
    (well_founded_ind InS_sublist_order_wf).
  intros phi sigma H1.
  eapply Seq_Forall_r.
  {
    apply InS_cons_I_hd.
    simpl.
    reflexivity.
  }
  eapply Seq_Forall_l with (t := Var 0).
  {
    apply InS_cons_I_hd.
    simpl.
    reflexivity.
  }
  {
    exact I.
  }
  eapply Seq_Impl_l.
  {
    apply InS_cons_I_hd.
    simpl.
    reflexivity.
  }
  {
    reflexivity.
  }
  -
    eapply Seq_Impl_r.
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    intros ns' H2.
    destruct (InS_sublist_dec ns ns') as [H3|H3].
    +
      eapply Seq_persistency.
      {
        apply InS_cons_I_hd.
        reflexivity.
      }
      {
        apply InS_cons_I_tl.
        apply InS_cons_I_tl.
        apply InS_cons_I_hd.
        split.
        -
          reflexivity.
        -
          repeat rewrite hsubst_comp'.
          apply H1.
          inversion 1; reflexivity.
      }
      exact H3.
    +
      apply Seq_weakening with
        (ls1 := (pair ns (CasariAnt phi).|[sigma].|[ren (+1)]) :: nil)
        (rs1 := (pair ns' (CasariSuc phi).|[sigma].|[ren (+1)]) :: nil).
      {
        intros psi H4.
        apply InS_cons_E in H4 as [H4|H4].
        -
          apply InS_cons_I_tl.
          apply InS_cons_I_tl.
          apply InS_cons_I_hd.
          rewrite H4.
          reflexivity.
        -
          now apply InS_nil_E in H4.
      }
      {
        intros psi H4.
        apply InS_cons_E in H4 as [H4|H4].
        -
          apply InS_cons_I_hd.
          rewrite H4.
          f_equiv.
          simpl.
          repeat rewrite hsubst_comp'.
          apply H1.
          inversion 1; reflexivity.
        -
          now apply InS_nil_E in H4.
      }
      eapply Seq_mon.
      {
        apply InS_cons_I_hd.
        reflexivity.
      }
      {
        exact H2.
      }
      eapply Seq_weakening with
        (ls1 := (pair ns' (CasariAnt phi).|[sigma].|[ren (+1)]) :: nil).
      {
        apply cons_InS_sublist_I.
        -
          apply InS_cons_I_hd.
          reflexivity.
        -
          apply nil_InS_sublist_I.
      }
      {
        reflexivity.
      }
      do 2 rewrite hsubst_comp'.
      eapply IH; try assumption.
      split; assumption.
  -
    eapply Seq_Forall_l with (t := Var 0).
    {
      apply InS_cons_I_hd.
      reflexivity.
    }
    {
      exact I.
    }
    eapply Seq_persistency.
    {
      left; reflexivity.
    }
    {
      left.
      f_equiv.
      repeat rewrite hsubst_comp'.
      apply H1.
      inversion 1; reflexivity.
    }
    reflexivity.
Qed.

Print Assumptions Seq_CasariAnt_CasariSuc.

Corollary Seq_Casari `{Signature} :
  forall phi ns,
    highest_occ_free_var phi (Some 0) ->
    Seq nil ((pair ns (Casari phi)) :: nil).
Proof.
  intros phi ns H1.
  eapply Seq_Impl_r.
  {
    apply InS_cons_I_hd.
    f_equiv.
    split; reflexivity.
  }
  intros ns' H2.
  eapply Seq_weakening with
    (ls1 := (pair ns' (CasariAnt phi).|[ids] :: nil))
    (rs1 := (pair ns' (CasariSuc phi).|[ids] :: nil)).
  {
    apply cons_InS_sublist_I.
    -
      apply InS_cons_I_hd.
      rewrite hsubst_id'.
      reflexivity.
    -
      apply nil_InS_sublist_I.
  }
  {
    apply cons_InS_sublist_I.
    -
      apply InS_cons_I_hd.
      rewrite hsubst_id'.
      reflexivity.
    -
      apply nil_InS_sublist_I.
  }
  eapply Seq_CasariAnt_CasariSuc.
  exact H1.
Qed.

Print Assumptions Seq_Casari.

Corollary support_valid_Casari_bd `{S : Signature} :
  forall phi ns,
    highest_occ_free_var phi (Some 0) ->
    forall (M : @Model S) f a,
      mapping_state f ns, a |= Casari phi.
Proof.
  intros phi ns H1 M f a.
  pose proof (Seq_Casari phi ns H1) as H2.
  apply soundness in H2.
  specialize (H2 _ f a (mult_nil_I _)).
  apply some_cons_E in H2 as [H2|H2].
  -
    exact H2.
  -
    now apply some_nil_E in H2.
Qed.

Print Assumptions support_valid_Casari_bd.
