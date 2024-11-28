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
      odd m &&
      (m =? j)
    ) ||
    (
      even m &&
      negb (j =? w) &&
      (
        odd j ||
        (m <? j)
      )
    ).

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

  Fact even_add : forall n, even (n + n) = true.
  Proof.
    intro n.
    assert (H1 : n + n = 0 + 2 * n). lia.
    rewrite H1.
    rewrite even_add_mul_2.
    reflexivity.
  Qed.

  Lemma claim_1 :
    forall s a m x,
      a x = 2 * m + 1 ->
      s, a |= <{IES x}>.
  Proof.
    intros s a m x H1.

    exists (2 * m + 1).

    intros w H2.
    asimpl in *.
    unfold rel.

    rewrite H1.
    rewrite odd_succ.
    rewrite even_add.
    rewrite eqb_refl.
    rewrite even_succ.
    unfold odd; rewrite even_add.
    reflexivity.
  Qed.

  Lemma claim_2 :
    forall (s : state) a m n x,
      s (2 * n + 1) = false ->
      a x = 2 * m ->
      s, a |= <{IES x}>.
  Proof.
    intros s a m n x H1 H2.

    exists (2 * n + 1).

    intros w H3.
    asimpl in *.
    unfold rel.

    rewrite H2.
    rewrite odd_succ.
    unfold odd.
    do 2 rewrite even_add.
    asimpl.
    destruct w as [|w'].
    -
      reflexivity.
    -
      destruct (n + n =? w') eqn:H4.
      +
        apply eqb_eq in H4.
        congruence.
      +
        reflexivity.
  Qed.

  Lemma claim_3 :
    forall (s : state) a m n x,
      s (2 * n) = false ->
      n > m ->
      a x = 2 * m ->
      s, a |= <{IES x}>.
  Proof.
    intros s a m n x H1 H2 H3.

    exists (2 * n).

    intros w H4.
    asimpl in *.
    unfold rel.

    rewrite H3.
    unfold odd.
    do 2 rewrite even_add.
    asimpl.
    destruct (n + n =? w) eqn:H5.
    -
      apply eqb_eq in H5.
      congruence.
    -
      destruct n as [|n'].
      +
        lia.
      +
        asimpl.
        apply leb_le.
        lia.
  Qed.

  Lemma claim_4 :
    forall (s : state) a m x,
      (
        forall w,
          odd w = true ->
          s w = true
      ) ->
      (
        forall w,
          even w = true ->
          2 * m <? w = true ->
          s w = true
      ) ->
      a x = 2 * m ->
      ~ (s, a |= <{IES x}>).
  Proof.
    intros s a m x H1 H2 H3 H4.

    assert (H5 : forall w j, rel w (m + m) j = true -> s j = true).
    {
      intros w j H5.
      unfold rel in H5.

      unfold odd in H5.
      rewrite even_add in H5.
      asimpl in H5.
      destruct (j =? w) eqn:H6.
      -
        apply eqb_eq in H6.
        subst j.
        discriminate.
      -
        destruct (even j) eqn:H7.
        +
          asimpl in H5.
          destruct j as [|j'].
          *
            discriminate.
          *
            apply H2.
            --
               exact H7.
            --
               asimpl.
               assumption.
        +
          apply H1.
          unfold odd.
          rewrite H7.
          reflexivity.
    }

    destruct H4 as [i H4].
    asimpl in H4.

    assert (H6 : rel i (m + m) i = false).
    {
      unfold rel.
      unfold odd.
      rewrite even_add.
      rewrite eqb_refl.
      reflexivity.
    }

    asimpl in H3.
    rewrite H3 in H4.
    rewrite H4 in H6. discriminate.

    eapply H5.
    apply H4.
    apply H1.
    exact odd_1.
  Qed.

End Casari_fails.
