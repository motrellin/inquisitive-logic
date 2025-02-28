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

(** * The Casari "counter-example" *)
Module Casari_fails.

  Import PeanoNat.Nat.

  (** ** Signature and Syntax *)

  Import Syntax_single_binary_predicate.

  Definition IES : form :=
    <{iexists (Pred' (Var 1) (Var 0))}>.

  Remark highest_occ_free_var_IES :
    highest_occ_free_var IES 0.
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

  (** ** The Model *)

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

  Lemma unnamed_helper_1 :
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

  (** ** Some state properties *)

  Lemma not_exists_forall_not {X} :
    forall (P : X -> Prop),
      ~ (exists x, P x) ->
      forall x,
        ~ P x.
  Proof.
    firstorder.
  Qed.

  (**
     CLA

     [not_forall_exists_not] depends on classical logic.

     Descendants:
     - [not_infinitely_many_finitely_many]
   *)
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

  Definition contains_all (p : nat -> bool) (s : state) : Prop :=
    forall w,
      p w = true ->
      s w = true.

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

  Definition contains_any (p : nat -> bool) (s : state) : Prop :=
    exists w,
      p w = true /\
      s w = true.

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

  Lemma substate_contains_any :
    forall p s t,
      substate t s ->
      contains_any p t ->
      contains_any p s.
  Proof.
    intros p s t H1 [w [H2 H3]].
    exists w.
    split.
    -
      exact H2.
    -
      apply H1.
      exact H3.
  Qed.

  Lemma not_contains_any_contains_all_complement :
    forall p s,
      ~ contains_any p s ->
      contains_all p (States.complement s).
  Proof.
    intros p s H1 w H2.
    apply complement_true.
    unfold contains_any in H1.
    apply not_exists_forall_not with (x := w) in H1.
    destruct (p w), (s w).
    all: firstorder.
  Qed.

  Definition finitely_many (p : nat -> bool) (s : state) : Prop :=
    exists e,
      forall w,
        p w = true ->
        s w = true ->
        w <=? e = true.

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

  Definition infinitely_many (p : nat -> bool) (s : state) : Prop :=
    forall w,
      exists e,
        p e = true /\
        s e = true /\
        w <? e = true.

  Lemma not_infinitely_many_finitely_many :
    forall p s,
      ~ infinitely_many p s ->
      finitely_many p s.
  Proof.
    intros p s H1.
    unfold infinitely_many in H1.
    red.
    apply not_forall_exists_not in H1 as [n H1].
    exists n.
    intros w H2 H3.
    apply not_exists_forall_not with (x := w) in H1.
    rewrite ltb_lt in H1.
    rewrite leb_le.
    destruct (p w), (s w).
    all: lia.
  Qed.

  Instance infinitely_many_Proper :
    forall p,
      Proper (state_eq ==> iff) (infinitely_many p).
  Proof.
    intros p s1 s2 H1.
    split.
    all: intros H2 w.
    all: specialize (H2 w) as [e H2].
    all: exists e.
    all: rewrite H1 in *.
    all: easy.
  Qed.

  Lemma substate_infinitely_many :
    forall p s t,
      substate t s ->
      infinitely_many p t ->
      infinitely_many p s.
  Proof.
    intros p s t H1 H2 n.
    destruct (H2 n) as [e [H3 [H4 H5]]].
    exists e.
    eauto using substate_contrapos.
  Qed.

  Local Definition E (s : state) : Prop :=
    contains_any (? ~ even ?) (States.complement s) \/
    infinitely_many even (States.complement s).

  Lemma substate_E :
    forall s t,
      substate t s ->
      E s ->
      E t.
  Proof.
    intros s t H1 [H2|H2].
    -
      left.
      eapply substate_contains_any.
      +
        apply substate_complement in H1.
        exact H1.
      +
        exact H2.
    -
      right.
      eapply substate_infinitely_many.
      +
        apply substate_complement in H1.
        exact H1.
      +
        exact H2.
  Qed.

  (** ** Support for [IES] *)

  (** [support_IES_odd] represents Claim 3.7. *)
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
     [support_IES_even], [support_IES_even_other_direction']
     and [support_IES_even_other_direction] represent
     Claim 3.8.
   *)
  Proposition support_IES_even :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      contains_any (? (~ even) || even && ltb (a 0) ?) (States.complement s) ->
      s, a |= IES.
  Proof.
    intros s a H1 [n [H2 H3]].

    apply complement_true in H3.

    exists n.
    simpl.
    intros w H4.

    unfold rel.
    rewrite H1.
    simpl.
    rewrite andb_true_iff.
    split.
    -
      destruct (n =? w) eqn:H5; try reflexivity.
      apply eqb_eq in H5.
      simpl in *.
      congruence.
    -
      apply orb_true_iff in H2 as [H2|H2].
      +
        rewrite H2.
        reflexivity.
      +
        apply andb_true_iff in H2 as [H21 H22].
        rewrite H21,H22.
        reflexivity.
  Qed.

  Print Assumptions support_IES_even.

  Lemma unnamed_helper_2 :
    forall (s : state) (m : nat),
      even m = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? ltb m ?) s ->
      forall w j,
        rel w m j = true ->
        s j = true.
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

  Lemma support_IES_even_other_direction' :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? ltb (a 0) ?) s ->
      ~ (s, a |= IES).
  Proof.
    intros s a H1 H2 H3 [i H4].
    asimpl in H4.

    pose proof (unnamed_helper_1 i _ H1) as H5.
    pose proof (unnamed_helper_2 _ _ H1 H2 H3) as H6.

    assert (H7 : s i = true).
    {
      apply H6 with (w := 1).
      apply H4.
      apply H2.
      reflexivity.
    }
    specialize (H4 _ H7).
    simpl in *.
    congruence.
  Qed.

  (**
     CLA

     [support_IES_even_other_direction] depends on classical
     logic.

     Descendants:
     - []
   *)
  Proposition support_IES_even_other_direction :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      s, a |= IES ->
      contains_any (? (~ even) || ltb (a 0) ?) (States.complement s).
  Proof.
    intros s a H1 H2.
    pose proof (support_IES_even_other_direction') as H3.
    specialize (H3 s a H1).

    apply NNPP.
    intros H4.

    apply not_contains_any_contains_all_complement in H4.
    rewrite complement_complement in H4.

    apply H3.
    -
      intros w H5.
      specialize (H4 w).
      rewrite orb_true_iff in H4.
      apply H4.
      left.
      exact H5.
    -
      intros w H5.
      apply H4.
      rewrite H5.
      rewrite orb_true_r.
      reflexivity.
    -
      exact H2.
  Qed.

  Print Assumptions support_IES_even_other_direction.

  (** ** Support for [CasariSuc IES] *)

  Proposition support_CasariSuc_IES :
    forall (s : state) (a : assignment),
      E s ->
      s, a |= <{ CasariSuc IES }>.
  Proof.
    intros s a H1 i.
    destruct (even i) eqn:H2.
    -
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
     [counter_state e] is a state that contains every odd number and every
     (even) number greater than [e]. By this, it contains at least one odd number
     and its complement can only contain infinitely many even numbers.
   *)
  Local Program Definition counter_state (e : nat) : state :=
    {|
      morph :=
        fun w =>
        if even w
        then e <? w
        else true
    |}.

  Fact counter_state_contains_all_odds :
    forall e,
      contains_all (? ~ even ?) (counter_state e).
  Proof.
    intros e w H1.
    simpl.
    destruct (even w); easy.
  Qed.

  Fact counter_state_contains_all_ltb :
    forall e,
      contains_all (? ltb e ?) (counter_state e).
  Proof.
    intros e w H1.
    simpl.
    destruct (even w); easy.
  Qed.

  Lemma support_CasariSuc_IES_other_direction' :
    forall (s : state) (a : assignment) (e : nat),
      contains_all (? ~ even ?) s ->
      contains_all (? ltb e ?) s ->
      ~ (s, a |= <{CasariSuc IES}>).
  Proof.
    intros s a e H1 H2 H3.

    unfold CasariSuc in H3.
    rewrite support_Forall in H3.

    eapply support_IES_even_other_direction' with
      (s := s)
      (a := (if even e then e else S e) .: a).
    -
      destruct (even e) eqn:H4.
      +
        exact H4.
      +
        remember ((S e .: a) 0) as n eqn:eq1.
        asimpl in eq1.
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
      asimpl in H4.
      destruct (even e).
      all: lia.
    -
      apply H3.
  Qed.

  Print Assumptions support_CasariSuc_IES_other_direction'.

  (**
     CLA

     [support_CasariSuc_IES_other_direction] depends on classical logic.

     Descendants:
     - [support_CasariImpl_IES_other_direction]
   *)
  Proposition support_CasariSuc_IES_other_direction :
    forall (s : state) (a : assignment),
      s, a |= <{ CasariSuc IES }> ->
      E s.
  Proof.
    intros s a H1.
    apply NNPP.
    intros H2.
    apply Decidable.not_or in H2 as [H2 H3].
    apply not_contains_any_contains_all_complement in H2.
    rewrite complement_complement in H2.

    apply not_infinitely_many_finitely_many in H3 as [e H3].

    eapply support_CasariSuc_IES_other_direction' with
      (e := e).
    -
      exact H2.
    -
      intros w H4.
      destruct (even w) eqn:H5.
      +
        specialize (H3 _ H5).
        rewrite complement_true in H3.
        rewrite ltb_lt in H4.
        rewrite leb_le in H3.
        destruct (s w); lia.
      +
        apply H2.
        rewrite H5.
        reflexivity.
    -
      exact H1.
  Qed.

  Print Assumptions support_CasariSuc_IES_other_direction.

  (** ** Support for [CasariImpl IES] *)

  Lemma support_CasariImpl_IES_even_other_direction' :
    forall (s : state) (a : assignment),
      even (a 0) = true ->
      contains_all (? ~ even ?) s ->
      finitely_many (? even ?) (States.complement s) ->
      contains_any (? ltb (a 0) ?) (States.complement s) ->
      ~ (s, a |= <{CasariImpl IES}>).
  Proof.
    intros s a H1 H2 [e1 H3] [e2 [H4 H5]] H6.

    eapply support_CasariSuc_IES_other_direction' with
      (e := e1).
    -
      exact H2.
    -
      intros w H7.
      destruct (even w) eqn:H8.
      +
        specialize (H3 _ H8).
        rewrite complement_true in H3.
        rewrite leb_le in H3.
        rewrite ltb_lt in H7.
        destruct (s w); lia.
      +
        apply H2.
        rewrite H8.
        reflexivity.
    -
      unfold CasariImpl in H6.
      rewrite support_Impl in H6.
      apply H6.
      +
        reflexivity.
      +
        apply support_IES_even.
        *
          exact H1.
        *
          exists e2.
          rewrite H4.
          split.
          --
             destruct (even e2); reflexivity.
          --
             exact H5.
  Qed.

  Print Assumptions support_CasariImpl_IES_even_other_direction'.

  Lemma unnamed_helper_3 :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      ~ E s ->
      exists t,
        substate t s /\
        contains_all (? ~ even ?) t /\
        finitely_many (? even ?) (States.complement t) /\
        contains_any (? ltb (a x) ?) (States.complement t).
  Proof.
    intros s a x H1 H2.
    apply Decidable.not_or in H2 as [H2 H3].
    apply not_contains_any_contains_all_complement in H2.
    rewrite complement_complement in H2.
    apply not_infinitely_many_finitely_many in H3 as [e H3].
    (**
       [e] is the greatest even number not in [s].
       We're looking for a [substate] [t] of [s], s.t.
       there also exists a greatest even number not in [t] and
       with one even number contained greater than [a x].
     *)
    unshelve eexists.
    {
      unshelve econstructor.
      exact (
        fun w =>
        if even w
        then S (S ((a x) + e)) <? w
        else true
      ).
      repeat intro.
      simpl in *.
      subst.
      reflexivity.
    }
    simpl.
    repeat split.
    -
      intros w H5.
      simpl in H5.
      destruct (even w) eqn:H4.
      +
        specialize (H3 _ H4).
        rewrite complement_true in H3.
        rewrite leb_le in H3.
        rewrite ltb_lt in H5.
        destruct (s w); lia.
      +
        apply H2.
        rewrite H4.
        reflexivity.
    -
      intros w H4.
      rewrite negb_true_iff in H4.
      simpl.
      rewrite H4.
      reflexivity.
    -
      exists (S (S (a x + e))).
      intros w H4 H5.
      simpl in H5.
      rewrite H4 in H5.
      apply leb_le.
      rewrite negb_true_iff in H5.
      apply ltb_nlt in H5.
      lia.
    -
      exists (S (S (a x))).
      rewrite complement_true.
      simpl.
      rewrite H1.
      split.
      +
        apply ltb_lt.
        lia.
      +
        apply ltb_nlt.
        lia.
  Qed.

  Print Assumptions unnamed_helper_3.

  (**
     CLA

     [support_CasariImpl_IES_other_direction] depends on classical logic.

     Descendants:
     - [support_CasariAnt_IES]
   *)
  Proposition support_CasariImpl_IES_other_direction :
    forall (s : state) (a : assignment),
      s, a |= <{CasariImpl IES}> ->
      E s.
  Proof.
    intros s a H1.
    destruct (even (a 0)) eqn:H2.
    -
      apply NNPP.
      intros H3.
      eapply (unnamed_helper_3 _ _ _ H2) in H3.
      destruct H3 as [t [H3 [H4 [H5 H6]]]].
      eapply support_CasariImpl_IES_even_other_direction'.
      all: eauto using persistency.
    -
      unfold CasariImpl in H1.
      rewrite support_Impl in H1.

      eapply support_CasariSuc_IES_other_direction.

      apply H1.
      +
        reflexivity.
      +
        apply support_IES_odd.
        exact H2.
  Qed.

  Print Assumptions support_CasariImpl_IES_other_direction.

  (** ** Support for [CasariAnt IES] *)

  Proposition support_CasariAnt_IES :
    forall (s : state) (a : assignment),
      s, a |= <{CasariAnt IES}>.
  Proof.
    intros s a i t H1 H2.
    apply support_CasariSuc_IES.
    eapply support_CasariImpl_IES_other_direction.
    exact H2.
  Qed.

  Print Assumptions support_CasariAnt_IES.

  (** ** Support for [Casari IES] *)

  Theorem not_support_valid_Casari_IES :
    ~ support_valid <{Casari IES}>.
  Proof.
    intros H1.

    eapply support_CasariSuc_IES_other_direction'.
    -
      apply counter_state_contains_all_odds.
    -
      apply counter_state_contains_all_ltb.
    -
      unfold Casari in H1.
      eapply H1.
      +
        reflexivity.
      +
        fold support.
        apply support_CasariAnt_IES.
    Unshelve.
    exact (fun _ => 25).
    exact 24.
  Qed.

  Print Assumptions not_support_valid_Casari_IES.
  (*
      Axioms:
        classic : forall P : Prop, P \/ ~ P
   *)

End Casari_fails.

(** * Bounded Casari *)

Scheme Equality for nat.

Proposition Seq_CasariAnt_CasariSuc `{Signature} :
  forall ns (phi : form) sigma,
    highest_occ_free_var phi 0 ->
    Seq
    ((pair ns (CasariAnt phi).|[sigma]) :: nil)
    ((pair ns (CasariSuc phi).|[sigma]) :: nil).
Proof.
  induction ns as [ns IH] using
    (well_founded_ind InS_sublist_order_wf).

  intros phi sigma H1.
  eapply Seq_Forall_r.
  -
    left; simpl; reflexivity.
  -
    eapply Seq_Forall_l with (t := Var 0).
    +
      left; simpl; reflexivity.
    +
      exact I.
    +
      eapply Seq_Impl_l.
      *
        left; simpl; reflexivity.
      *
        reflexivity.
      *
        eapply Seq_Impl_r.
        --
           left; reflexivity.
        --
           intros ns' H2.
           destruct (InS_sublist_dec ns ns') as [H3|H3].
           ++
              eapply prop_4_6.
              **
                 left; reflexivity.
              **
                 apply InS_cons_I_tl.
                 apply InS_cons_I_tl.
                 apply InS_cons_I_hd.
                 simpl.
                 split.
                 ---
                     simpl.
                     reflexivity.
                 ---
                     simpl.
                     enough (H4 :
                      phi.|[Var 0 .: sigma >> ren (+1)] ==
                      phi.|[up sigma]
                     ).
                     {
                       repeat rewrite hsubst_comp'.
                       apply H1.
                       intros [|y'] H5; lia + reflexivity.
                     }
                     apply H1.
                     inversion 1; reflexivity.
              **
                 exact H3.
           ++
              apply Seq_weakening with
                (ls1 := (pair ns (CasariAnt phi).|[sigma].|[ren (+1)]) :: nil)
                (rs1 := (pair ns' (CasariSuc phi).|[sigma].|[ren (+1)]) :: nil).
              **
                 intros psi H4.
                 apply InS_cons_E in H4 as [H4|H4].
                 ---
                     apply InS_cons_I_tl.
                     apply InS_cons_I_tl.
                     apply InS_cons_I_hd.
                     rewrite H4.
                     reflexivity.
                 ---
                     contradict H4.
                     apply InS_nil_E.
              **
                 intros psi H4.
                 apply InS_cons_E in H4 as [H4|H4].
                 ---
                     apply InS_cons_I_hd.
                     rewrite H4.
                     simpl.
                     split.
                     +++
                         reflexivity.
                     +++
                         simpl.
                         enough (H5 :
                           phi.|[ids 0 .: sigma >> ren (+2)] ==
                           phi.|[upn 2 sigma]
                         ).
                         {
                           repeat rewrite hsubst_comp'.
                           apply H1.
                           intros [|y'] H6; try lia.
                           reflexivity.
                         }
                         (*
                         ) by (rewrite H5; reflexivity).
                          *)

                         apply H1.
                         inversion 1; reflexivity.
                 ---
                     contradict H4.
                     apply InS_nil_E.
              **
                 eapply Seq_mon.
                 ---
                     left; reflexivity.
                 ---
                     exact H2.
                 ---
                     eapply Seq_weakening with
                       (ls1 := (pair ns' (CasariAnt phi).|[sigma].|[ren (+1)]) :: nil).
                     +++
                         apply cons_InS_sublist_I.
                         ***
                             apply InS_cons_I_hd.
                             reflexivity.
                         ***
                             apply nil_InS_sublist_I.
                     +++
                         reflexivity.
                     +++
                         do 2 rewrite hsubst_comp'.
                         eapply IH; try assumption.
                         simpl in H2.
                         split.
                         ***
                             exact H2.
                         ***
                             exact H3.
      *
        eapply Seq_Forall_l with (t := Var 0).
        --
           left; reflexivity.
        --
           exact I.
        --
           eapply prop_4_6.
           ++
              left; reflexivity.
           ++
              left.
              simpl.
              split.
              **
                 reflexivity.
              **
                 enough (H2 :
                  phi.|[Var 0 .: up sigma] == phi.|[up sigma]
                 ).
                 {
                   red in H1.
                   repeat rewrite hsubst_comp'.
                   apply H1.
                   intros [|y'] H3; try lia.
                   reflexivity.
                 }
                 (*
                 ) by (rewrite H2; reflexivity).
                  *)
                 apply H1.
                 inversion 1; reflexivity.
           ++
              reflexivity.
Qed.

Print Assumptions Seq_CasariAnt_CasariSuc.

Corollary Seq_Casari `{Signature} :
  forall phi ns,
    highest_occ_free_var phi 0 ->
    Seq nil ((pair ns (Casari phi)) :: nil).
Proof.
  intros phi ns H1.
  eapply Seq_Impl_r.
  -
    left.
    split.
    +
      simpl.
      reflexivity.
    +
      simpl snd.
      unfold Casari.
      reflexivity.
  -
    intros ns' H2.
    eapply Seq_weakening with
      (ls1 := (pair ns' (CasariAnt phi).|[ids] :: nil))
      (rs1 := (pair ns' (CasariSuc phi).|[ids] :: nil)).
    +
      apply cons_InS_sublist_I.
      *
        apply InS_cons_I_hd.
        split; try reflexivity.
        simpl.
        repeat split.
        --
           transitivity (phi.|[ids]).
           ++
              apply H1.
              intros [|y'] H3; try lia.
              reflexivity.
           ++
              apply hsubst_id'.
        --
           transitivity (phi.|[ids]).
           ++
              apply H1.
              intros [|y'] H3; try lia.
              reflexivity.
           ++
              apply hsubst_id'.
        --
           transitivity (phi.|[ids]).
           ++
              apply H1.
              intros [|y'] H3; try lia.
              reflexivity.
           ++
              apply hsubst_id'.
      *
        apply nil_InS_sublist_I.
    +
      intros psi H3.
      apply InS_cons_E in H3 as [H3|H3].
      *
        apply InS_cons_I_hd.
        rewrite H3.
        split.
        --
           reflexivity.
        --
           simpl.
           transitivity (phi.|[ids]).
           ++
              apply H1.
              intros [|y'] H4; try lia.
              reflexivity.
           ++
              apply hsubst_id'.
      *
        contradict H3.
        apply InS_nil_E.
    +
      eapply Seq_CasariAnt_CasariSuc.
      exact H1.
Qed.

Print Assumptions Seq_Casari.

Corollary support_valid_Casari_bd `{S : Signature} :
  forall phi ns,
    highest_occ_free_var phi 0 ->
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
    contradict H2.
    apply some_nil_E.
Qed.

Print Assumptions support_valid_Casari_bd.
