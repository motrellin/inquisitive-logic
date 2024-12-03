From InqLog Require Export Truth.

From Coq Require Import Nat Bool Lia PeanoNat.
Import PeanoNat.Nat.

(** * Casari Scheme *)

Definition Casari `{Signature} (phi : var -> form) : form :=
  <{
    (
      forall
      (
        (
          (
            phi 0
          ) ->
          (
            forall (phi 0)
          )
        ) ->
        (
          forall (phi 0)
        )
      )
    ) ->
    (
      forall (phi 0)
    )
  }>.

Lemma Casari_truth_conditional `{Signature} :
  forall phi,
    (forall x, classic (phi x) = true) ->
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

    intros s2 H1 H2.

    apply substate_singleton in H1 as [H1|H1]; rewrite H1 in *; clear s2 H1.
    now apply empty_state_property.

    intros i1.
    rewrite support_Neg.
    intros [s3 [[w2 H3] [H4 H5]]].

    enough (
      exists s,
        (s, (i1 .: a) |= <{forall ~~(Pred' (Var 0))}>) /\
        substate s3 s
    ) as [s4 [H6 H7]].
    {
      specialize (H6 i1). fold support in H6.

      rewrite support_Neg in H6.
      apply H6.
      exists s3.
      firstorder.
    }

    specialize (H2 i1). fold support in H2.
    remember <{~~(Pred' (Var 0))}> as phi1 eqn:eq1.
    remember <{forall phi1}> as phi2 eqn:eq2.
    remember <{phi1 -> phi2}> as phi3 eqn:eq3.


    eexists.
    split.

    apply H2. exact H4.

    fold support.
    subst phi3.

    apply substate_singleton in H4 as [H4|H4]; rewrite H4 in *; clear s3 H4.
    now apply empty_state_property.

    intros s4 H6 H7.

    apply substate_singleton in H6 as [H6|H6]; rewrite H6 in *; clear s4 H6.
    now apply empty_state_property.

    exfalso.

    rewrite eq1 in H7.
    rewrite support_Neg in H7.
    apply H7.

    eexists.
    repeat split.
    -
      eexists.
      exact H3.
    -
      reflexivity.
    -
      exact H5.
    -
      reflexivity.
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

Module Casari_fails.

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

  Definition CasariIES := Casari IES.

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

  Lemma claim_1 :
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

  Lemma claim_2 :
    forall (s : state) (a : assignment) (x : var) (n : nat),
      even (a x) = true ->
      even n = false ->
      s n = false ->
      s, a |= <{IES x}>.
  Proof.
    intros s a x n H1 H2 H3.

    exists n.

    asimpl.
    intros w H4.
    unfold rel.

    rewrite H2.
    rewrite H1.
    asimpl.
    destruct (n =? w) eqn:H5.
    -
      apply eqb_eq in H5.
      congruence.
    -
      reflexivity.
  Qed.

  Lemma claim_3 :
    forall (s : state) (a : assignment) (x : var) (n : nat),
      even (a x) = true ->
      even n = true ->
      s n = false ->
      n > a x ->
      s, a |= <{IES x}>.
  Proof.
    intros s a x n H1 H2 H3 H4.

    exists n.

    intros w H5.
    asimpl in *.
    unfold rel.

    rewrite H1.
    rewrite H2.
    simpl.
    destruct (n =? w) eqn:H6.
    -
      apply eqb_eq in H6.
      congruence.
    -
      apply ltb_lt in H4.
      rewrite H4.
      reflexivity.
  Qed.

  Definition contains_all_odds (s : state) : Prop :=
    forall w,
      even w = false ->
      s w = true.

  Definition contains_all_even_greater_than (m : nat) (s : state) : Prop :=
    forall w,
      even w = true ->
      m <? w = true ->
      s w = true.

  Lemma claim_4_helper :
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

  Lemma claim_4 :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_all_odds s ->
      contains_all_even_greater_than (a x) s ->
      ~ (s, a |= <{IES x}>).
  Proof.
    intros s a x H1 H2 H3 H4.

    pose proof (claim_4_helper _ _ H1 H2 H3) as H5.

    destruct H4 as [i H4].
    asimpl in H4.

    pose proof (rel_2 i _ H1) as H6.

    rewrite H4 in H6. discriminate.

    apply H5 with (w := 1).
    apply H4.
    apply H2.
    reflexivity.
  Qed.

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
        s e = false /\
        n <? e = true.

  Lemma substate_contains_inf_evens :
    forall s t,
      substate t s ->
      contains_inf_evens s ->
      contains_inf_evens t.
  Proof.
    intros s t H1 H2 n.
    destruct (H2 n) as [e [H3 [H4 H5]]].
    exists e.
    eauto using substate_contrapos.
  Qed.

  Local Definition E (s : state) : Prop :=
    contains_no_odd s \/
    contains_inf_evens s.

  Lemma substate_E :
    forall s t,
      substate t s ->
      E s ->
      E t.
  Proof.
    intros s t H1 [H2|H2].
    -
      left.
      eauto using substate_contains_no_odd.
    -
      right.
      eauto using substate_contains_inf_evens.
  Qed.

  Proposition support_Forall_IES :
    forall (s : state) (a : assignment),
      E s ->
      s, a |= <{ forall (IES 0) }>.

  (* It seems like this direction could be sufficient for the first. For the
   * conclusion at the end of the proof, it should be enough to show, that there
   * exists a counterexample s.t. not every state supports <{ forall (IES 0) }>.
   * Edit: No, it isn't enough.
   *)
  Proof.
    intros s a H1 i.
    destruct (even i) eqn:H2.
    -
      destruct H1 as [H1|H1].
      +
        apply claim_2 with (n := 1).
        *
          exact H2.
        *
          reflexivity.
        *
          apply H1.
          reflexivity.
      +
        destruct (H1 i) as [e [H3 [H4 H5]]].
        apply ltb_lt in H5.
        eapply claim_3.
        *
          exact H2.
        *
          exact H3.
        *
          exact H4.
        *
          simpl.
          lia.
    -
      eapply claim_1.
      exact H2.
  Qed.

  Proposition support_Forall_IES_other_direction :
    forall (s : state) (a : assignment),
      s, a |= <{ forall (IES 0) }> ->
      E s.
  Proof.
    intros s a H1.
    asimpl in H1.
    red.
    (* This doesn't look nice. Let's admit this for now. *)
  Admitted.

  (* What about this (classically equivalent) proposition? *)

  Proposition support_Forall_IES_other_direction' :
    forall (s : state) (a : assignment) (n1 n2 : nat),
      even n1 = false ->
      s n1 = true ->
      (forall e,
        even e = false \/
        s e = true \/
        e <=? n2 = true
      ) ->
      ~ (s, a |= <{ forall (IES 0) }>).
  Proof.
    intros s a n1 n2 H1 H2 H3 H4.

    remember (IES 0) as phi.
    simpl in H4.
    subst phi.

    specialize (H4 n1).
    asimpl in H4.
    destruct H4 as [i H4].
  Abort.

  Local Definition counter_state : state :=
    fun w =>
    if even w
    then 0 <? w
    else true.

  Example not_support_Forall_IES :
    forall (a : assignment),
      ~ (counter_state, a |= <{forall IES 0}>).
  Proof.
    intros a H1.

    remember (IES 0) as phi.
    simpl in H1.
    subst phi.

    eapply claim_4 with (s := counter_state) (a := 0 .: a) (x := 0).
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

  Proposition support_odd_IES_Forall_IES :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = false ->
      E s ->
      s, a |= <{IES x -> forall IES 0}>.
  Proof.
    intros s a x H1 H2.
    intros t H3 H4.

    eauto using support_Forall_IES, substate_E.
  Qed.

  Proposition support_odd_IES_Forall_IES_other_direction :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = false ->
      s, a |= <{IES x -> forall IES 0}> ->
      E s.
  Proof.
    intros s a x H1 H2.
    eapply support_Forall_IES_other_direction.
    remember (<{forall IES 0}>) as phi.
    apply H2.
    -
      reflexivity.
    -
      fold support.
      apply claim_1.
      exact H1.
  Qed.

  Proposition support_odd_CasariIES_ant :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = false ->
      s, a |= <{(IES x -> forall IES 0) -> forall IES 0}>.
  Proof.
    intros s a x H1.

    intros t H2 H3.

    apply support_Forall_IES.
    (*
       Here we see, why we need the other direction... TODO

        s : state
        a : assignment
        x : var
        H1 : even (a x) = true
        t : state
        H2 : substate t s
        H3 : t, a |= <{ (IES x) -> (forall (IES 0)) }>

        ========================= (1 / 1)

        E t
     *)
    eapply support_odd_IES_Forall_IES_other_direction.
    -
      exact H1.
    -
      exact H3.
  Qed.

  Proposition support_even_IES_Forall_IES :
    forall (s : state) (a : assignment) (x : var),
      even x = true ->
      E s ->
      s, a |= <{IES x -> forall IES 0}>.
  Proof.
    intros s a x H1 H2.
    intros t H3 H4.
    apply support_Forall_IES.
    right.
    intros n.
  Admitted.

End Casari_fails.
