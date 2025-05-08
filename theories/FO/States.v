From InqLog Require Export ListLib.
From InqLog.FO Require Export Models.

(** * Basic definitions

   We now introduce the notion of a [state] which can be seen a set of worlds in a model.
 *)

Definition state `{Model} :=
  Morph World bool.

(**
   We define a predicate [contains] to improve readability.
 *)
Definition contains `{Model} (s : state) (w : World) : Prop :=
  s w = true.

Lemma contains_dec `{Model} :
  forall s w,
    {contains s w} + {~ contains s w}.
Proof.
  intros s w.
  unfold contains.
  destruct (s w); [left|right]; congruence.
Qed.

(** ** Substates

   This section implements the notion of substates in a typical set-theoretic way.
 *)
Definition substate `{Model} : relation state :=
  fun t s =>
  forall w,
    contains t w ->
    contains s w.

(**
   [substate] is a [PreOrder] which is a [reflexive] and [transitive] [relation], at least, if we follow the way, Coq defines it as such.
 *)
Print PreOrder.

Instance substate_PreOrder `{Model} : PreOrder substate.
Proof.
  split.
  -
    (* Reflexivity *)
    intros s w H1.
    exact H1.
  -
    (* Transitivity *)
    intros s1 s2 s3 H1 H2 w H3.
    auto.
Qed.

Instance contains_Proper_substate `{Model} :
  Proper (substate ==> equiv ==> impl) contains.
Proof.
  intros t s H1 w1 w2 H2 H3.
  unfold contains in *.
  rewrite H2 in H3.
  apply H1.
  exact H3.
Qed.

Lemma substate_contrapos `{Model} :
  forall s t w,
    substate t s ->
    ~ contains s w ->
    ~ contains t w.
Proof.
  intros s t w H1 H2 H3.
  apply H2.
  apply H1.
  exact H3.
Qed.

(** ** Equivalence/Equality of States

   As we typically just care whether two states behave the same, we introduce this as a relation [state_eq], which is indeed an equivalence relation.
 *)
Definition state_eq `{Model} : relation state :=
  Morph_eq.

(**
   [contains] respects [state_eq].
 *)
Instance contains_Proper `{Model} :
  Proper (state_eq ==> equiv ==> iff) contains.
Proof.
  intros s1 s2 H1 w1 w2 H2.
  unfold contains.
  rewrite H1,H2.
  reflexivity.
Qed.

(**
   For every [s : state], [contains s] is a morphism.
 *)
Program Definition contains_Morph `{Model} (s : state) : Morph World Prop :=
  {|
    morph := contains s
  |}.

Lemma contains_iff_contains_Morph `{Model} :
  forall s w,
    contains s w <->
    contains_Morph s w.
Proof.
  reflexivity.
Qed.

(**
   [substate] respects [state_eq].
 *)
Instance substate_Proper `{Model} :
  Proper (state_eq ==> state_eq ==> iff) substate.
Proof.
  intros s1 s2 H1 t1 t2 H2.
  split.
  all: intros H3 w H4.
  all: rewrite <- H2 + rewrite H2.
  all: apply H3.
  all: rewrite H1 + rewrite <- H1.
  all: exact H4.
Qed.

Lemma state_eq_iff_contains `{Model} :
  forall s1 s2,
    s1 == s2 <->
    forall w,
      contains s1 w <->
      contains s2 w.
Proof.
  intros s1 s2.
  unfold contains.
  split.
  all: intros H1 w.
  -
    rewrite H1.
    reflexivity.
  -
    specialize (H1 w).
    destruct (s1 w),(s2 w).
    all: intuition.
Qed.

Lemma state_eq_iff_substate `{Model} :
  forall s1 s2,
    state_eq s1 s2 <->
    substate s1 s2 /\ substate s2 s1.
Proof.
  intros s1 s2.
  split.
  -
    intros H1.
    rewrite H1.
    split.
    all: reflexivity.
  -
    intros [H1 H2].
    apply state_eq_iff_contains.
    intros w.
    split.
    all: intros H3.
    all: rewrite <- H1 + rewrite <- H2.
    all: exact H3.
Qed.

(** ** Consistent States

   A state is called _consistent_ if it contains at least one world.
 *)
Definition consistent `{Model} (s : state) : Prop :=
  exists w,
    contains s w.

(**
   [consistent] respects [substate].
 *)
Instance consistent_Proper_substate `{Model} :
  Proper (substate ==> impl) consistent.
Proof.
  intros s1 s2 H1 [w H2].
  exists w.
  rewrite <- H1.
  exact H2.
Qed.

(**
   [consistent] respects [state_eq].
 *)
Instance consistent_Proper `{Model} :
  Proper (state_eq ==> iff) consistent.
Proof.
  intros s1 s2 H1.
  apply state_eq_iff_substate in H1 as [H1 H2].
  split.
  all: intros H3.
  all: rewrite <- H1 + rewrite <- H2.
  all: exact H3.
Qed.

(** * Example States *)
(** ** The Empty State *)

Program Definition empty_state `{Model} : state :=
  {|
    morph := fun _ => false
  |}.

Next Obligation.
  easy.
Qed.

Lemma contains_empty_state_E `{Model} :
  forall w,
    ~ contains empty_state w.
Proof.
  discriminate.
Qed.

(**
   [empty_state] is a substate of every state.
 *)
Lemma empty_state_substate_I `{Model} :
  forall t,
    substate empty_state t.
Proof.
  intros t w H1.
  now apply contains_empty_state_E in H1.
Qed.

(**
   The only substate of the empty state is the empty state.
 *)
Lemma substate_empty_state_E `{Model} :
  forall t,
    substate t empty_state ->
    t == empty_state.
Proof.
  intros t H1.
  apply state_eq_iff_contains.
  intros w.
  split.
  all: intros H2.
  -
    rewrite <- H1.
    exact H2.
  -
    now apply contains_empty_state_E in H2.
Qed.

(**
   It it quite obvious that the empty state is the only inconsistent state.
 *)
Remark state_eq_empty_state_iff_not_consistent `{Model} :
  forall s,
    s == empty_state <->
    ~ consistent s.
Proof.
  intros s.
  split.
  -
    intros H1 [w H2].
    rewrite H1 in H2.
    now apply contains_empty_state_E in H2.
  -
    intros H1.
    apply state_eq_iff_contains.
    intros w.
    split.
    all: intros H2.
    +
      contradict H1.
      now exists w.
    +
      now apply contains_empty_state_E in H2.
Qed.

(** ** The Most Inconsistent (nonempty) State *)

Program Definition most_inconsistent `{Model} :
  state :=

  {|
    morph := fun _ => true
  |}.

Next Obligation.
  repeat intro; reflexivity.
Qed.

Lemma contains_most_inconsistent_I `{Model} :
  forall w,
    contains most_inconsistent w.
Proof.
  intros w.
  reflexivity.
Qed.

(**
   Every state is a substate of [most_inconsistent].
 *)
Lemma substate_most_inconsistent_I `{Model} :
  forall t,
    substate t most_inconsistent.
Proof.
  intros t w H1.
  apply contains_most_inconsistent_I.
Qed.

(**
   If [most_inconsistent] is a substate of another state [t], then [t] must be [most_inconsistent].
 *)
Lemma most_inconsistent_substate_E `{Model} :
  forall t,
    substate most_inconsistent t ->
    t == most_inconsistent.
Proof.
  intros t H1.
  apply state_eq_iff_contains.
  intros w.
  split.
  all: intros H2.
  -
    apply contains_most_inconsistent_I.
  -
    rewrite <- H1.
    exact H2.
Qed.

Lemma consistent_most_inconsistent_I `{Model} :
  World ->
  consistent most_inconsistent.
Proof.
  intros w.
  exists w.
  apply contains_most_inconsistent_I.
Qed.

(** ** Singleton States *)

Program Definition singleton `{Model} (w : World) : state :=
  {|
    morph :=
      fun w' => w' ==b w
   |}.

Next Obligation.
  intros w1 w2 H1.
  unfold "_ ==b _".
  destruct (w1 == w) as [H2|H2].
  all: destruct (w2 == w) as [H3|H3].
  all: reflexivity + rewrite H1 in H2; contradiction.
Qed.

Lemma contains_singleton_iff `{Model} :
  forall w w',
    contains (singleton w) w' <->
    w' == w.
Proof.
  intros w w'.
  unfold contains; simpl; unfold "_ ==b _".
  destruct (w' == w) as [H1|H1].
  all: easy.
Qed.

Lemma not_contains_singleton_iff `{Model} :
  forall w w',
    ~ contains (singleton w) w' <->
    w' =/= w.
Proof.
  intros w w'.
  simpl.
  unfold contains; simpl; unfold "_ ==b _".
  destruct (w' == w) as [H1|H1].
  all: easy.
Qed.

Lemma contains_singleton_refl `{Model} :
  forall w,
    contains (singleton w) w.
Proof.
  intros w.
  rewrite contains_singleton_iff.
  reflexivity.
Qed.

(**
   [singleton w] is substate of every state containing [w].
 *)
Lemma singleton_substate_iff `{Model} :
  forall (s : state) w,
    substate (singleton w) s <->
    contains s w.
Proof.
  intros s w.
  split.
  -
    intros H1.
    rewrite <- H1.
    apply contains_singleton_refl.
  -
    intros H1 w' H2.
    apply contains_singleton_iff in H2.
    rewrite H2.
    exact H1.
Qed.

(**
   If a state is substate of a [singleton] state then it
   must be the singleton state itself or the empty state.
 *)
Lemma substate_singleton_E `{Model} :
  forall w t,
    substate t (singleton w) ->
    (
      t == empty_state \/
      t == (singleton w)
    ).
Proof.
  intros w t H1.
  (**
     Case distinction whether the world [w] is part of [t]
     or not.
   *)
  destruct (contains_dec t w) as [H2|H2].
  -
    right.
    symmetry.
    apply state_eq_iff_contains.
    intros w'.
    rewrite contains_singleton_iff.
    split.
    all: intros H3.
    +
      rewrite H3.
      exact H2.
    +
      apply contains_singleton_iff.
      rewrite <- H1.
      exact H3.
  -
    left.
    apply state_eq_iff_contains.
    intros w'.
    split.
    all: intros H3.
    +
      contradict H2.
      apply H1 in H3 as H4.
      apply contains_singleton_iff in H4.
      rewrite <- H4.
      exact H3.
    +
      now apply contains_empty_state_E in H3.
Qed.

Instance singleton_Proper `{Model} :
  Proper (equiv ==> state_eq) singleton.
Proof.
  intros w1 w2 H1.
  apply state_eq_iff_contains.
  intros w.
  do 2 rewrite contains_singleton_iff.
  rewrite H1.
  reflexivity.
Qed.

Lemma consistent_singleton_I `{Model} :
  forall w,
    consistent (singleton w).
Proof.
  intros w.
  exists w.
  apply contains_singleton_refl.
Qed.

(** ** Complement states *)

Program Definition complement `{Model} (s : state) : state :=
  {|
    morph := fun w => negb (s w)
  |}.

Next Obligation.
  intros w1 w2 H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma contains_complement_iff `{Model} :
  forall s w,
    contains (complement s) w <->
    ~ contains s w.
Proof.
  intros s w.
  unfold contains; simpl.
  rewrite negb_true_iff,not_true_iff_false.
  reflexivity.
Qed.

Lemma not_contains_complement_iff `{Model} :
  forall s w,
    ~ contains (complement s) w <->
    contains s w.
Proof.
  intros s w.
  apply eq_true_negb_classical_iff.
Qed.

Instance complement_Proper_substate `{Model} :
  Proper (substate --> substate) complement.
Proof.
  intros s1 s2 H1 w H2.
  apply contains_complement_iff.
  apply contains_complement_iff in H2.
  eapply substate_contrapos; eassumption.
Qed.

(**
   The [substate] relation turns around for [complement]
   states.
 *)
Lemma complement_substate_complement_iff `{Model} :
  forall s t,
    substate (complement s) (complement t) <->
    substate t s.
Proof.
  intros s t.
  split.
  -
    intros w H1 H2.
    apply not_contains_complement_iff.
    apply not_contains_complement_iff in H2.
    eapply substate_contrapos.
    all: eassumption.
  -
    intros H1.
    rewrite H1.
    reflexivity.
Qed.

Instance complement_Proper `{Model} :
  Proper (state_eq ==> state_eq) complement.
Proof.
  intros s1 s2 H1 w.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

Lemma complement_involutive `{Model} :
  forall s,
    (complement (complement s)) == s.
Proof.
  intros s w.
  apply negb_involutive.
Qed.

(** ** Excluding states

   Excluding states implement the idea that we want to be
   able to exclude a world from a state.
 *)

Program Definition excluding_state `{Model} (s : state) (w : World) : state :=
  {|
    morph :=
      fun w' =>
      if w' == w
      then false
      else s w'
  |}.

Next Obligation.
  intros w1 w2 H1.
  destruct (w1 == w) as [H2|H2].
  all: destruct (w2 == w) as [H3|H3].
  all: rewrite H1 in *; reflexivity + contradiction.
Qed.

Lemma contains_excluding_state_iff `{Model} :
  forall s w w',
  contains (excluding_state s w) w' <->
  contains s w' /\
  w' =/= w.
Proof.
  intros s w w'.
  unfold contains.
  simpl.
  split.
  -
    intros H1.
    destruct (w' == w) as [H2|H2]; try discriminate.
    split.
    all: assumption.
  -
    intros [H1 H2].
    destruct (w' == w) as [H3|_]; try contradiction.
    exact H1.
Qed.

Lemma not_contains_excluding_state_iff `{Model} :
  forall s w w',
    ~ contains (excluding_state s w) w' <->
    ~ contains s w' \/
    w' == w.
Proof.
  intros s w w'.
  split.
  -
    intros H1.
    destruct (contains_dec s w') as [H2|H2]; try (left; exact H2).
    destruct (w' == w) as [H3|H3]; try (right; exact H3).
    exfalso.
    apply H1.
    apply contains_excluding_state_iff.
    split.
    all: assumption.
  -
    intros [H1|H1] H2.
    all: apply contains_excluding_state_iff in H2 as [H2 H3].
    all: contradiction.
Qed.

(**
   An excluding state is always a substate of its original
   state.
 *)
Lemma excluding_state_substate_I `{Model} :
  forall s w,
    substate (excluding_state s w) s.
Proof.
  intros s w w' H1.
  apply contains_excluding_state_iff in H1 as [H1 H2].
  exact H1.
Qed.

(**
   If the original state [s] does not contain a World [w],
   then excluding [w] from [s] has no effect.
 *)
Lemma excluding_state_irrelevance `{Model} :
  forall (s : state) w,
    ~ contains s w ->
    (excluding_state s w) == s.
Proof.
  intros s w H1.
  apply state_eq_iff_contains.
  intros w'.
  rewrite contains_excluding_state_iff.
  split.
  -
    now firstorder.
  -
    intros H2.
    split; try assumption.
    intros H3.
    rewrite H3 in H2.
    contradiction.
Qed.

(** ** Mapping States

   Mapping states implement the idea that we can describe finite states via (finite) lists of natural numbers and a mapping function.
 *)

Program Definition mapping_state `{Model} (f : nat -> World) (ns : list nat) : state :=
  {|
    morph :=
    flip inbS (map f ns)
  |}.

Next Obligation.
  induction ns as [|n ns' IH].
  all: intros w1 w2 H1.
  all: unfold flip.
  -
    reflexivity.
  -
    simpl.
    unfold "_ ==b _".
    destruct (w1 == f n) as [H2|H2].
    all: destruct (w2 == f n) as [H3|H3].
    all: simpl.
    all: try (rewrite H1 in H2; contradiction).
    all: try reflexivity.

    apply IH.
    exact H1.
Qed.

Lemma contains_mapping_state_I `{Model} :
  forall f ns n,
    InS n ns ->
    contains (mapping_state f ns) (f n).
Proof.
  intros f ns n H1.
  apply InS_iff_inbS_true.
  apply InS_map_I.
  exact H1.
Qed.

Lemma contains_mapping_state_E `{Model} :
  forall f ns w,
    contains (mapping_state f ns) w ->
    exists n,
      f n == w /\
      InS n ns.
Proof.
  intros f ns w H1.
  apply InS_iff_inbS_true in H1.
  apply InS_map_E in H1.
  exact H1.
Qed.

Lemma contains_mapping_state_iff `{Model} :
  forall f ns w,
    contains (mapping_state f ns) w <->
    exists n,
      f n == w /\
      InS n ns.
Proof.
  intros f ns w.
  split.
  -
    apply contains_mapping_state_E.
  -
    intros [n [H1 H2]].
    rewrite <- H1.
    apply contains_mapping_state_I.
    exact H2.
Qed.

(**
   [mapping_state] also respects [Morph_eq] and [InS_sublist].
 *)
Instance mapping_state_Proper_substate `{Model} :
  Proper (ext_eq ==> InS_sublist ==> substate) mapping_state.
Proof.
  intros f1 f2 H1 ns1 ns2 H2 w H3.
  apply contains_mapping_state_E in H3 as [n [H3 H4]].
  specialize (H1 n).
  rewrite H1 in H3.
  rewrite <- H3.
  apply contains_mapping_state_I.
  apply H2.
  exact H4.
Qed.

Lemma substate_mapping_state_E `{Model} :
  forall f ns t,
  substate t (mapping_state f ns) ->
  exists ns',
    t == (mapping_state f ns') /\
    InS_sublist ns' ns.
Proof.
  intros f ns t H1.
  exists (filter (fun n => t (f n)) ns).
  split.
  -
    apply state_eq_iff_substate.
    split.
    +
      intros w H2.
      apply H1 in H2 as H3.
      apply contains_mapping_state_E in H3 as [n [H3 H4]].
      rewrite <- H3.
      apply contains_mapping_state_I.
      apply InS_filter_I.
      *
        rewrite <- H3 in H2.
        exact H2.
      *
        exact H4.
    +
      intros w H2.
      apply contains_mapping_state_E in H2 as [n [H2 H3]].
      rewrite <- H2.
      apply InS_filter_E in H3 as [H3 H4].
      exact H3.
  -
    apply filter_InS_sublist_I.
Qed.

(**
   [mapping_state] respects [Morph_eq] and [InS_eq].
 *)
Instance mapping_state_Proper `{Model} :
  Proper (ext_eq ==> InS_eq ==> state_eq) mapping_state.
Proof.
  intros f1 f2 H1 ns1 ns2 [H2 H3].
  apply state_eq_iff_substate.
  split.

  all: apply mapping_state_Proper_substate.
  all: try assumption.
  symmetry; assumption.
Qed.

Lemma mapping_state_nil_state_eq_empty_state `{Model} :
  forall f,
    (mapping_state f nil) == empty_state.
Proof.
  intros f w.
  reflexivity.
Qed.

(** * Restricting a [Model] to a [state] *)

Program Definition restricted_Model `{M : Model} (s : state) : Model :=
  {|
    World_Setoid := sig_Setoid (contains_Morph s);
    Individual := Individual;
    Individual_inh := Individual_inh;
    Individual_deceq := Individual_deceq;
    PInterpretation :=
      fun w =>
      PInterpretation (proj1_sig w);
    FInterpretation :=
      fun w =>
      FInterpretation (proj1_sig w)
 |}.

Next Obligation.
  (**
     [PInterpretation] has to respect the defined equality
     for worlds.
   *)
  repeat intro.
  apply PInterpretation_Proper_outer.
  assumption.
Qed.

Next Obligation.
  (**
     [FInterpretation] has to respect the defined equality
     for worlds.
   *)
  repeat intro.
  apply FInterpretation_Proper_outer.
  assumption.
Qed.

Next Obligation.
  (**
     Rigidity is directly gained from the original model.
   *)
  apply rigidity.
  assumption.
Qed.

(**
   Next step: We define how we can translate states from the
   original model to our defined restricted model.
 *)
Program Definition restricted_state
  `{Model}
  (s t : state) :
  @state _ (restricted_Model s) :=

  {|
    morph := fun w =>
      s (proj1_sig w) && t (proj1_sig w)
  |}.

Next Obligation.
  intros w1 w2 H1.
  red in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma contains_restricted_state_iff `{Model} :
  forall s t w,
    contains (restricted_state s t) w <->
    contains s (proj1_sig w) /\ contains t (proj1_sig w).
Proof.
  intros s t w.
  unfold contains.
  simpl.
  apply andb_true_iff.
Qed.

Program Definition unrestricted_state `{Model} (s : state) (t : @state _ (restricted_Model s)) : state :=
  {|
    morph :=
      fun w =>
      match contains_dec s w with
      | left H => t (exist (contains_Morph s) _ H)
      | right _ => false
      end
 |}.

Next Obligation.
  intros w1 w2 H1.
  destruct (contains_dec s w1) as [H2|H2].
  all: destruct (contains_dec s w2) as [H3|H3].
  -
    apply sig_eq_lifting with
      (P := contains_Morph s)
      (C1 := H2)
      (C2 := H3)
      in H1
      as H4.
    rewrite H4.
    reflexivity.
  -
    contradict H3.
    rewrite <- H1.
    exact H2.
  -
    contradict H2.
    rewrite H1.
    exact H3.
  -
    reflexivity.
Qed.

Lemma contains_unrestricted_state_iff `{Model} :
  forall s t w (C1 : contains s w),
    contains (unrestricted_state s t) w <->
    contains t (exist (contains_Morph s) _ C1).
Proof.
  intros s t w C1.
  unfold contains.
  simpl.
  destruct (contains_dec s w) as [H1|H1].
  -
    assert (H2 : w == w) by reflexivity.
    apply sig_eq_lifting with
      (P := contains_Morph s)
      (C1 := C1)
      (C2 := H1)
      in H2.
    rewrite H2.
    reflexivity.
  -
    contradiction.
Qed.

Lemma not_contains_unrestricted_state_I_domain `{Model} :
  forall s t w,
    ~ contains s w ->
    ~ contains (unrestricted_state s t) w.
Proof.
  intros s t w H1 H2.
  unfold contains in H2.
  simpl in H2.
  destruct (contains_dec s w) as [H3|H3].
  -
    contradiction.
  -
    discriminate.
Qed.

Lemma unrestricted_substate `{Model} :
  forall s1 s2 s3,
    substate s3 (restricted_state s1 s2) ->
    substate (unrestricted_state s1 s3) s2.
Proof.
  intros * H1 w H2.
  destruct (contains_dec s1 w) as [H3|H3].
  -
    apply contains_unrestricted_state_iff with (C1 := H3) in H2.
    apply H1 in H2.
    apply contains_restricted_state_iff in H2 as [H21 H22].
    exact H22.
  -
    apply not_contains_unrestricted_state_I_domain with (t := s3) in H3.
    contradiction.
Qed.

Lemma state_eq_restricted_state_unrestricted_state `{Model}:
  forall s t,
    t == (restricted_state s (unrestricted_state s t)).
Proof.
  intros s t.
  apply state_eq_iff_contains.
  intros [w H1].
  rewrite contains_restricted_state_iff.
  split.
  -
    intros H2.
    split.
    +
      exact H1.
    +
      apply contains_unrestricted_state_iff in H2.
      exact H2.
  -
    intros [H2 H3].
    apply contains_unrestricted_state_iff.
    exact H3.
Qed.
