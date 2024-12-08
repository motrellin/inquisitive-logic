From InqLog Require Export Truth.

From Coq Require Import Nat Bool Lia PeanoNat Classical_Prop.
Import PeanoNat.Nat.

(** * The Casari Scheme *)

Definition CasariSuc `{Signature} (phi : var -> form) : form :=
  <{ forall (phi 0) }>.

Definition CasariImpl `{Signature} (phi : var -> form) (x : var) : form :=
  <{phi x -> CasariSuc phi}>.

Definition CasariAnt `{Signature} (phi : var -> form) : form :=
  <{ forall CasariImpl phi 0 -> CasariSuc phi }>.

Definition Casari `{Signature} (phi : var -> form) : form :=
  <{ CasariAnt phi -> CasariSuc phi }>.

Lemma Casari_truth_conditional `{Signature} :
  forall phi,
    (forall x, Syntax.classic (phi x) = true) ->
    truth_conditional (Casari phi).
Proof.
  intros phi H1.
  apply classic_truth_conditional.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

(** * Some Casari Instances with atomic predicates *)

Module Casari_with_atoms.

  Instance signature : Signature :=
    {|
      PSymb := unit;
      PAri := fun p => match p with tt => unit end;
      FSymb := Empty_set;
      FAri := fun f => match f with end;
      rigid := fun _ => true
    |}.

  Definition Pred' (t : term) := Pred tt (fun arg => t).

  Definition CasariDNA : form :=
    Casari (fun x => Neg (Neg (Pred' (Var x)))).

  Definition CasariAtomic : form :=
    Casari (fun x => Pred' (Var x)).

  Remark CasariDNA_Prop (P : var -> Prop) :
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

  Theorem truth_CasariDNA `{@Model signature} :
    forall w a,
      truth CasariDNA w a.
  Proof.
    intros w1 a.

    unfold CasariDNA, Casari.

    rewrite truth_Impl.
    intros H1.

    unfold CasariSuc.

    rewrite truth_Forall.
    intros i.

    rewrite truth_Neg.
    intros H2.

    enough (H3 : truth <{ forall ~ ~ Pred' (Var 0)}> w1 a).
    {
      rewrite truth_Forall in H3.
      specialize (H3 i).
      rewrite truth_Neg in H3.
      contradiction.
    }

    unfold CasariAnt in H1.
    rewrite truth_Forall in H1.
    specialize (H1 i).
    rewrite truth_Impl in H1.
    apply H1.

    unfold CasariImpl.
    rewrite truth_Impl.
    intros H3.

    rewrite truth_Neg in H3.
    contradiction.
  Qed.

  Corollary support_valid_CasariDNA :
    support_valid CasariDNA.
  Proof.
    intros M s a.
    apply Casari_truth_conditional.
    -
      reflexivity.
    -
      intros w H1.
      apply truth_CasariDNA.
  Qed.

  Theorem support_conseq_CasariDNA_CasariAtomic :
    support_conseq CasariDNA CasariAtomic.
  Proof.
    unfold CasariDNA.
    unfold CasariAtomic.
    unfold Casari.

    apply support_conseq_Impl.
    apply support_conseq_Forall.
    apply support_conseq_Impl.
    apply support_conseq_Impl.

    firstorder.

    apply support_conseq_Forall.

    apply support_valid_Impl_conseq.
    intros *.
    apply support_valid_DNE_Pred.

    apply support_conseq_Forall.

    firstorder.

    apply support_conseq_Forall.
    apply support_valid_Impl_conseq.
    intros *.
    apply support_valid_DNE_Pred.
  Qed.

  Corollary support_valid_CasariAtomic :
    support_valid CasariAtomic.
  Proof.
    eapply support_valid_conseq_valid.
    -
      exact support_valid_CasariDNA.
    -
      exact support_conseq_CasariDNA_CasariAtomic.
  Qed.

End Casari_with_atoms.

(** * The Casari "counter-example" *)
Module Casari_fails.

  (** ** Signature and Syntax *)

  Instance signature : Signature :=
    {|
      PSymb := unit;
      PAri := fun p => match p with tt => bool end;
      FSymb := Empty_set;
      FAri := fun f => match f with end;
      rigid := fun _ => true
    |}.

  Definition Pred' (l r : term) :=
    Pred tt (fun arg => if arg then l else r).

  Definition IES (x : var) : form :=
    <{iexists (Pred' (Var (x+1)) (Var 0))}>.

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

  Lemma rel_odd :
    forall w m j,
      even m = false ->
      rel w m j = true ->
      j = m.
  Proof.
    intros w m j H1 H2.
    unfold rel in H2.
    apply orb_true_iff in H2 as [H2|H2].
    -
      apply andb_true_iff in H2 as [H2 H3].
      apply eqb_eq in H3.
      congruence.
    -
      rewrite H1 in H2.
      discriminate.
  Qed.

  Lemma rel_2 :
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
      Individual := nat;
      Individual_inh := 42;
      PInterpretation :=
        fun w p =>
        match p with
        | tt =>
            fun args =>
            rel w (args true) (args false)
        end
    |}.

  (** ** Some state properties *)

  Definition contains_all_odds (s : state) : Prop :=
    forall w,
      even w = false ->
      s w = true.

  Definition contains_all_even_greater_than (m : nat) (s : state) : Prop :=
    forall w,
      even w = true ->
      m <? w = true ->
      s w = true.

  Definition contains_no_odd (s : state) : Prop :=
    forall w,
      even w = false ->
      s w = false.

  Lemma substate_contains_no_odd :
    forall s t,
      substate t s ->
      contains_no_odd s ->
      contains_no_odd t.
  Proof.
    intros s t H1 H2 w H3.
    eauto using substate_contrapos.
  Qed.

  Definition contains_inf_evens (s : state) : Prop :=
    forall n,
      exists e,
        even e = true /\
        s e = true /\
        n <? e = true.

  Lemma substate_contains_inf_evens :
    forall s t,
      substate t s ->
      contains_inf_evens t ->
      contains_inf_evens s.
  Proof.
    intros s t H1 H2 n.
    destruct (H2 n) as [e [H3 [H4 H5]]].
    exists e.
    eauto using substate_contrapos.
  Qed.

  Local Definition E (s : state) : Prop :=
    contains_no_odd s \/
    contains_inf_evens (complement s).

  Lemma substate_E :
    forall s t,
      substate t s ->
      E s ->
      E t.
  Proof.
    intros s t H1 [H2|H2].
    -
      left.
      eapply substate_contains_no_odd.
      +
        exact H1.
      +
        exact H2.
    -
      right.
      apply substate_complement in H1.
      eapply substate_contains_inf_evens.
      +
        exact H1.
      +
        exact H2.
  Qed.

  Definition cofinitely_many (s : state) (p : nat -> bool) : Prop :=
    exists e,
      forall w,
        p w = true ->
        e <? w = true ->
        s w = true.

  (** ** Support for [IES] *)

  Proposition support_IES_odd :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = false ->
      s, a |= <{IES x}>.
  Proof.
    intros s a x H1.

    exists (a x).

    intros w H2.
    asimpl.
    unfold rel.

    rewrite H1.
    rewrite eqb_refl.
    reflexivity.
  Qed.

  Proposition support_IES_even :
    forall (s : state) (a : assignment) (x : var) (n : nat),
      even (a x) = true ->
      s n = false ->
      (even n = false \/ even n = true /\ a x <? n = true) ->
      s, a |= <{IES x}>.
  Proof.
    intros s a x n H1 H2 H3.
    exists n.
    simpl.
    intros w H4.
    asimpl.
    unfold rel.
    rewrite H1.
    simpl.
    rewrite andb_true_iff.
    split.
    -
      destruct (n =? w) eqn:H5.
      +
        apply eqb_eq in H5.
        congruence.
      +
        reflexivity.
    -
      destruct H3 as [H3|[H31 H32]].
      +
        rewrite H3.
        reflexivity.
      +
        rewrite H31,H32.
        reflexivity.
  Qed.

  Lemma unnamed_helper_2 :
    forall (s : state) (m : nat),
      even m = true ->
      contains_all_odds s ->
      contains_all_even_greater_than m s ->
      forall w j,
        rel w m j = true ->
        s j = true.
  Proof.
    intros s m H1 H2 H3.
    intros w j H5.
    unfold rel in H5.

    rewrite H1 in H5.
    simpl in H5.
    destruct (j =? w) eqn:H6.
    -
      discriminate.
    -
      destruct (even j) eqn:H7.
      all: auto.
  Qed.

  Lemma support_IES_even_other_direction' :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_all_odds s ->
      contains_all_even_greater_than (a x) s ->
      ~ (s, a |= <{IES x}>).
  Proof.
    intros s a x H1 H2 H3 H4.

    pose proof (unnamed_helper_2 _ _ H1 H2 H3) as H5.

    destruct H4 as [i H4].
    asimpl in H4.

    pose proof (rel_2 i _ H1) as H6.

    rewrite H4 in H6. discriminate.

    apply H5 with (w := 1).
    apply H4.
    apply H2.
    reflexivity.
  Qed.

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

  Proposition support_IES_even_other_direction :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      s, a |= <{IES x}> ->
      exists n,
        s n = false /\
        (
          even n = false \/
          even n = true /\
          a x <? n = true
        ).
  Proof.
    intros s a x H1 H2.
    pose proof (support_IES_even_other_direction') as H3.
    specialize (H3 s a x H1).

    apply NNPP.
    intros H4.

    assert (H4' :
      forall n,
        ~ (s n = false /\ (even n = false \/ even n = true /\ (a x <? n) = true))
    ). firstorder.
    clear H4. rename H4' into H4.

    assert (H4' :
      forall n,
        s n = true \/ (even n = true /\ (even n = false \/ a x <? n = false))
    ).
    {
      intros n.
      specialize (H4 n).
      destruct (s n), (even n), (a x <? n).
      all: firstorder.
    }
    clear H4. rename H4' into H4.

    apply H3.
    -
      intros w H5.
      specialize (H4 w) as [H4|[H41 H42]].
      +
        exact H4.
      +
        congruence.
    -
      intros w H5 H6.
      specialize (H4 w) as [H4|[H41 [H42|H42]]].
      +
        exact H4.
      +
        congruence.
      +
        congruence.
    -
      exact H2.
  Qed.

  (** ** Support for [CasariSuc IES] *)

  Proposition support_CasariSuc_IES :
    forall (s : state) (a : assignment),
      E s ->
      s, a |= <{ CasariSuc IES }>.
  Proof.
    intros s a H1 i.
    destruct (even i) eqn:H2.
    -
      destruct H1 as [H1|H1].
      +
        apply support_IES_even with (n := 1).
        *
          exact H2.
        *
          apply H1.
          reflexivity.
        *
          left.
          reflexivity.
      +
        destruct (H1 i) as [e [H3 [H4 H5]]].
        eapply support_IES_even.
        *
          exact H2.
        *
          apply complement_true.
          exact H4.
        *
          right.
          split.
          --
             exact H3.
          --
             exact H5.
    -
      eapply support_IES_odd.
      exact H2.
  Qed.

  Local Definition counter_state : state :=
    fun w =>
    if even w
    then 0 <? w
    else true.

  Example cex_support_valid_CasariSuc_IES :
    forall (a : assignment),
      ~ (counter_state, a |= <{CasariSuc IES}>).
  Proof.
    intros a H1.

    unfold CasariSuc in H1.
    rewrite support_Forall in H1.

    eapply support_IES_even_other_direction' with (s := counter_state) (a := 0 .: a) (x := 0).
    -
      reflexivity.
    -
      intros w H2.

      unfold counter_state.
      rewrite H2.
      reflexivity.
    -
      intros w H2 H3.

      unfold counter_state.
      rewrite H2.
      exact H3.
    -
      apply H1.
  Qed.

  Proposition support_CasariSuc_IES_other_direction :
    forall (s : state) (a : assignment),
      s, a |= <{ CasariSuc IES }> ->
      E s.
  Proof.
    intros s a H1.
    asimpl in H1.
    red.
    (* This doesn't look nice. Let's admit this for now. *)
  Admitted.

  (* What about this (classically equivalent) proposition? *)
  Lemma support_CasariSuc_IES_other_direction' :
    forall (s : state) (a : assignment) (n1 n2 : nat),
      even n1 = false ->
      s n1 = true ->
      (forall e,
        even e = false \/
        s e = true \/
        e <=? n2 = true
      ) ->
      ~ (s, a |= <{ CasariSuc IES }>).
  Proof.
    intros s a n1 n2 H1 H2 H3 H4.

    unfold CasariSuc in H4.
    rewrite support_Forall in H4.

    specialize (H4 n1).
    asimpl in H4.
    destruct H4 as [i H4].
  Abort.

  Lemma unnamed_helper_1 :
    forall (s : state) (a : assignment),
      contains_all_odds s ->
      cofinitely_many s even ->
      ~ (s, a |= <{CasariSuc IES}>).
  Proof.
    intros s a H1 H2 H3.
    apply support_CasariSuc_IES_other_direction in H3 as [H3|H3].
    -
      specialize (H1 1 Logic.eq_refl).
      specialize (H3 1 Logic.eq_refl).
      congruence.
    -
      red in H3.
      destruct H2 as [e H2].
      specialize (H3 e) as [n [H4 [H5 H6]]].
      rewrite complement_true in H5.
      specialize (H2 _ H4 H6).
      congruence.
  Qed.

  (** ** Support for [CasariImpl IES] *)

  Lemma support_CasariImpl_IES_even_case_other_direction' :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_all_odds s ->
      cofinitely_many s even ->
      (forall w,
        s w = true ->
        even w = true ->
        w <=? a x = true
      ) ->
      ~ (s, a |= <{CasariImpl IES x}>).
  Proof.
    intros s a x H1 H2 H3 H4 H5.
    unfold CasariImpl in H5.

    eapply unnamed_helper_1; try eassumption.

    rewrite support_Impl in H5.
    apply H5.
    -
      reflexivity.
    -
      apply support_IES_even with (n := (a x) + 2).
      +
        exact H1.
      +
        destruct (s ((a x) + 2)) eqn:H7; try reflexivity.
        apply H4 in H7.
        *
          apply leb_le in H7.
          lia.
        *
          asimpl.
          exact H1.
      +
        right.
        split.
        *
          asimpl.
          exact H1.
        *
          apply ltb_lt.
          lia.
  Qed.

  Proposition support_CasariImpl_IES_other_direction :
    forall (s : state) (a : assignment) (x : var),
      s, a |= <{CasariImpl IES x}> ->
      E s.
  Proof.
    intros s a x H1.
    destruct (even (a x)) eqn:H2.
    -
      unfold CasariImpl in H1.
      rewrite support_Impl in H1.
      admit.
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
  Admitted.

  (** ** Support for [CasariAnt IES] *)

  Proposition support_CasariAnt_IES :
    forall (s : state) (a : assignment),
      s, a |= <{CasariAnt IES}>.
  Proof.
    intros s a i.
    intros t H1 H2.
    apply support_CasariSuc_IES.
    eapply support_CasariImpl_IES_other_direction.
    exact H2.
  Qed.

  (** ** Support for [Casari IES] *)

  Theorem not_support_valid_Casari_IES :
    ~ support_valid <{Casari IES}>.
  Proof.
    intros H1.

    specialize (H1 _ counter_state id).

    eapply cex_support_valid_CasariSuc_IES.

    unfold Casari in H1.
    rewrite support_Impl in H1.
    apply H1.
    -
      reflexivity.
    -
      apply support_CasariAnt_IES.
  Qed.

  Print Assumptions not_support_valid_Casari_IES.
  (*
      Axioms:
      support_CasariImpl_IES_other_direction
        : forall (s : state) (a : assignment) (x : var),
          s, a |= CasariImpl IES x -> E s
   *)

End Casari_fails.
