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
      contains_all p (complement s).
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
  Admitted.

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
    contains_any (? ~ even ?) (complement s) \/
    infinitely_many even (complement s).

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

  (**
     [support_IES_even], [support_IES_even_other_direction'] and
     [support_IES_even_other_direction] represent Claim 3.8.
   *)
  Proposition support_IES_even :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_any (? (~ even) || even && ltb (a x) ?) (complement s) ->
      s, a |= <{IES x}>.
  Proof.
    intros s a x H1 [n [H2 H3]].

    rewrite orb_true_iff in H2.
    rewrite andb_true_iff in H2.
    apply complement_true in H3.

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
      destruct H2 as [H2|[H21 H22]].
      +
        rewrite H2.
        reflexivity.
      +
        rewrite H21,H22.
        reflexivity.
  Qed.

  Lemma unnamed_helper_2 :
    forall (s : state) (m : nat),
      even m = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? even && ltb m ?) s ->
      forall w j,
        rel w m j = true ->
        s j = true.
  Proof.
    intros s m H1 H2 H3 w j H4.

    unfold rel in H4.
    rewrite H1 in H4.
    simpl in H4.
    destruct (j =? w) eqn:H6.
    -
      discriminate.
    -
      simpl in H4.
      destruct (even j) eqn:H7.
      +
        apply H3.
        apply andb_true_iff.
        auto.
      +
        apply H2.
        rewrite H7.
        reflexivity.
  Qed.

  Lemma support_IES_even_other_direction' :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_all (? ~ even ?) s ->
      contains_all (? even && ltb (a x) ?) s ->
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

  Proposition support_IES_even_other_direction :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      s, a |= <{IES x}> ->
      contains_any (? (~ even) || even && ltb (a x) ?) (complement s).
  Proof.
    intros s a x H1 H2.
    pose proof (support_IES_even_other_direction') as H3.
    specialize (H3 s a x H1).

    apply NNPP.
    intros H4.

    apply not_contains_any_contains_all_complement in H4.
    rewrite complement_complement in H4.

    apply H3.
    -
      intros w H5.
      specialize (H4 w).
      rewrite orb_true_iff in H4.
      rewrite andb_true_iff in H4.
      apply H4.
      left.
      exact H5.
    -
      intros w H5.
      rewrite andb_true_iff in H5.
      destruct H5 as [H5 H6].
      apply H4.
      rewrite H5.
      rewrite H6.
      reflexivity.
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
          simpl.
          rewrite H3,H4,H5.
          split; reflexivity.
    -
      eapply support_IES_odd.
      exact H2.
  Qed.

  (**
     [counter_state e] is a state that contains every odd number and every
     (even) number greater than [e]. By this, it contains at least one odd number
     and its complement can only contain infinitely many even numbers.
   *)
  Local Definition counter_state (e : nat) : state :=
    fun w =>
    if even w
    then e <? w
    else true.

  Fact counter_state_contains_all_odds :
    forall e,
      contains_all (? ~ even ?) (counter_state e).
  Proof.
    intros e w H1.
    unfold counter_state.
    destruct (even w); easy.
  Qed.

  Fact counter_state_contains_all_even_greater_than :
    forall e,
      contains_all (? even && ltb e ?) (counter_state e).
  Proof.
    intros e w H1.
    rewrite andb_true_iff in H1.
    destruct H1 as [H1 H2].
    unfold counter_state.
    rewrite H1,H2.
    reflexivity.
  Qed.

  Lemma support_CasariSuc_IES_other_direction' :
    forall (s : state) (a : assignment) (e : nat),
      contains_all (? ~ even ?) s ->
      contains_all (? even && ltb e ?) s ->
      ~ (s, a |= <{CasariSuc IES}>).
  Proof.
    intros s a e H1 H2 H3.

    unfold CasariSuc in H3.
    rewrite support_Forall in H3.

    eapply support_IES_even_other_direction' with
      (s := s)
      (a := (if even e then e else S e) .: a)
      (x := 0).
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
      intros w H4.

      apply H1.
      exact H4.
    -
      intros w H4.
      apply andb_true_iff in H4 as [H4 H5].
      apply H2.
      apply andb_true_iff.
      split.
      +
        exact H4.
      +
        apply ltb_lt in H5.
        apply ltb_lt.
        asimpl in H5.
        destruct (even e).
        all: lia.
    -
      apply H3.
  Qed.

  Proposition support_CasariSuc_IES_other_direction :
    forall (s : state) (a : assignment),
      s, a |= <{ CasariSuc IES }> ->
      E s.
  Proof.
    intros s a H1.
    red.
    apply NNPP.
    intros H2.
    apply Decidable.not_or in H2 as [H2 H3].
    apply not_contains_any_contains_all_complement in H2.
    rewrite complement_complement in H2.

    apply not_infinitely_many_finitely_many in H3 as [e H3].

    apply support_CasariSuc_IES_other_direction' with (e := e) in H1.
    -
      exact H1.
    -
      exact H2.
    -
      intros w H4.
      apply andb_true_iff in H4 as [H4 H5].
      specialize (H3 w H4).
      rewrite complement_true in H3.
      rewrite ltb_lt in H5.
      rewrite leb_le in H3.
      destruct (s w); lia.
  Qed.

  (** ** Support for [CasariImpl IES] *)

  Lemma support_CasariImpl_IES_even_other_direction' :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      contains_all (? ~ even ?) s ->
      finitely_many (? even ?) (complement s) ->
      contains_any (? even && ltb (a x) ?) (complement s) ->
      ~ (s, a |= <{CasariImpl IES x}>).
  Proof.
    intros s a x H1 H2 [e1 H3] [e2 [H4 H6]] H7.
    apply andb_true_iff in H4 as [H4 H5].
    unfold CasariImpl in H7.

    eapply support_CasariSuc_IES_other_direction' with
      (e := e1).
    -
      exact H2.
    -
      intros w H8.
      apply andb_true_iff in H8 as [H8 H9].
      specialize (H3 w H8).
      rewrite complement_true in H3.
      rewrite leb_le in H3.
      rewrite ltb_lt in H9.
      destruct (s w).
      all: lia.
    -
      rewrite support_Impl in H7.
      apply H7.
      +
        reflexivity.
      +
        apply support_IES_even.
        *
          exact H1.
        *
          exists e2.
          simpl.
          rewrite H4.
          simpl.
          split.
          --
             exact H5.
          --
             exact H6.
  Qed.

  Lemma unnamed_helper_4 :
    forall (s : state) (a : assignment) (x : var),
      even (a x) = true ->
      ~ E s ->
      exists t,
        substate t s /\
        contains_all (? ~ even ?) t /\
        finitely_many (? even ?) (complement t) /\
        contains_any (? even && ltb (a x) ?) (complement t).
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
    eexists (
      fun w =>
      if even w
      then S (S ((a x) + e)) <? w
      else true
    ).
    repeat split.
    -
      intros w H5.
      destruct (even w) eqn:H6.
      +
        specialize (H3 w H6).
        rewrite complement_true in H3.
        rewrite leb_le in H3.
        rewrite ltb_lt in H5.
        destruct (s w); lia.
      +
        apply H2.
        rewrite H6.
        reflexivity.
    -
      intros w H4.
      rewrite negb_true_iff in H4.
      rewrite H4.
      reflexivity.
    -
      exists (S (S (a x + e))).
      intros w H4 H5.
      rewrite complement_true in H5.
      rewrite H4 in H5.
      apply leb_le.
      apply ltb_nlt in H5.
      lia.
    -
      exists (S (S (a x))).
      rewrite andb_true_iff.
      rewrite complement_true.
      simpl.
      rewrite H1.
      repeat split.
      +
        apply ltb_lt.
        lia.
      +
        apply ltb_nlt.
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
      apply NNPP.
      intros H3.
      eapply unnamed_helper_4 in H3 as [t [H3 [H4 [H5 H6]]]]; try eassumption.
      eapply support_CasariImpl_IES_even_other_direction'.
      +
        exact H2.
      +
        exact H4.
      +
        exact H5.
      +
        exact H6.
      +
        eapply persistency.
        *
          exact H1.
        *
          exact H3.
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

    eapply support_CasariSuc_IES_other_direction'.
    -
      apply counter_state_contains_all_odds.
    -
      apply counter_state_contains_all_even_greater_than.
    -
      unfold Casari in H1.
      apply support_valid_Impl_conseq in H1.
      apply H1.
      apply support_CasariAnt_IES.
    Unshelve.
    exact 0.
    exact id.
  Qed.

  Print Assumptions not_support_valid_Casari_IES.
  (*
      Axioms:
        classic : forall P : Prop, P \/ ~ P
   *)

End Casari_fails.
