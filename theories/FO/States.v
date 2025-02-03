From InqLog Require Export ListBib.
From InqLog.FO Require Export Models.

From Coq Require Export Bool.

(** * Basic definitions

   We now introduce the notion of a [state] which is just a
   set of worlds in a model.
 *)

Print Instances Setoid.

Definition state `{Model} := Morph World bool.

(**
   As we typically just care whether two states behave the
   same, we introduce this as a relation [state_eq], which
   is indeed an equivalence relation.
 *)
Definition state_eq `{Model} : relation state := Morph_eq.

Instance state_eq_Equiv `{Model} : Equivalence state_eq.
Proof.
  split.
  -
    (* Reflexivity *)
    intros s w.
    reflexivity.
  -
    (* Symmetry *)
    intros s t H1 w.
    rewrite H1.
    reflexivity.
  -
    (* Transitivity *)
    intros s t u H1 H2 w.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

(** * Example states *)
(** ** The empty state *)

Program Definition empty_state `{Model} : state :=
  {|
    morph := fun _ => false
  |}.

Next Obligation.
  easy.
Qed.

(** ** Singleton states *)

Program Definition singleton `{Model} (w : World) : state :=
  {|
    morph :=
      fun w' =>
      if w' == w
      then true
      else false
   |}.

Next Obligation.
  intros w1 w2 H1.
  destruct (w1 == w) as [H2|H2].
  all: destruct (w2 == w) as [H3|H3].
  all: reflexivity + rewrite H1 in H2; contradiction.
Qed.

Proposition singleton_true `{Model} :
  forall w w',
    singleton w w' = true <->
    w' == w.
Proof.
  intros w w'.
  simpl.
  destruct (w' == w) as [H1|H1].
  all: easy.
Qed.

Proposition singleton_false `{Model} :
  forall w w',
    singleton w w' = false <->
    w' =/= w.
Proof.
  intros w w'.
  simpl.
  destruct (w' == w) as [H1|H1].
  all: easy.
Qed.

Proposition singleton_refl `{Model} :
  forall w,
    singleton w w = true.
Proof.
  intros w.
  rewrite singleton_true.
  reflexivity.
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

Fact complement_true `{Model} :
  forall s w,
    complement s w = true <->
    s w = false.
Proof.
  intros s w.
  apply negb_true_iff.
Qed.

Fact complement_false `{Model} :
  forall s w,
    complement s w = false <->
    s w = true.
Proof.
  intros s w.
  apply negb_false_iff.
Qed.

Fact complement_complement `{Model} :
  forall s,
    state_eq (complement (complement s)) s.
Proof.
  intros s w.
  apply negb_involutive.
Qed.

(** ** Mapping states *)

Program Definition mapping_state
  `{Model}
  (f : Morph nat World)
  (ns : list nat) :
  state :=

  {|
    morph :=
    fun w =>
    inbS w (map f ns)
  |}.

Next Obligation.
  induction ns as [|n ns' IH].
  all: intros w1 w2 H1.
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

Instance mapping_state_Proper `{Model} :
  Proper (Morph_eq ==> InS_eq ==> state_eq) mapping_state.
Proof.
  intros f1 f2 H1 ns1 ns2 H2.
  intros w.
  simpl.
  apply InS_iff_inbS.
  red in H1.
  split.
  all: intros H3.
  all: apply InS_map_E in H3 as [n [H3 H4]].
  all: rewrite <- H3.
  all: rewrite H1 + rewrite <- H1.
  all: apply InS_map_I.
  all: apply H2.
  all: exact H4.
Qed.

Lemma mapping_state_nil `{Model} :
  forall f,
    state_eq (mapping_state f nil) empty_state.
Proof.
  intros f w.
  reflexivity.
Qed.

Lemma mapping_state_cons `{Model} :
  forall f n ns' w,
    mapping_state f (n :: ns') w =
    (w ==b (f n)) ||
    mapping_state f ns' w.
Proof.
  intros f n ns' w.
  reflexivity.
Qed.

(** ** Excluding states *)

Program Definition excluding_state `{Model} (s : state) (w : World) : state :=
  {|
    morph :=
      fun w' =>
      if w == w'
      then false
      else s w'
  |}.

Next Obligation.
  intros w1 w2 H1.
  destruct (w == w1) as [H2|H2].
  all: destruct (w == w2) as [H3|H3].
  all: rewrite H1 in *; reflexivity + contradiction.
Qed.

Lemma unnamed_helper_States_1 `{Model} :
  forall (s : state) w,
    s w = false ->
    state_eq (excluding_state s w) s.
Proof.
  intros s w H1 w'.
  simpl.
  destruct (w == w') as [H2|H2].
  -
    rewrite H2 in H1.
    congruence.
  -
    reflexivity.
Qed.

(** * Consistent states *)

Definition consistent `{Model} (s : state) : Prop := exists w, s w = true.

Fact empty_state_not_consistent `{Model} :
  forall s,
    state_eq s empty_state <->
    ~ consistent s.
Proof.
  intros s.
  split.
  -
    intros H1 [w H2].
    rewrite H1 in H2.
    discriminate.
  -
    intros H1 w.
    destruct (s w) eqn:H2; try reflexivity.
    exfalso.
    apply H1.
    exists w.
    exact H2.
Qed.

Fact singleton_consistent `{Model} :
  forall w,
    consistent (singleton w).
Proof.
  intros w.
  exists w.
  apply singleton_true.
  reflexivity.
Qed.

(** * Substates *)

Definition substate `{Model} : relation state :=
  fun t s =>
  forall w,
    t w = true -> s w = true.

Lemma substate_contrapos `{Model} :
  forall s t w,
    substate t s ->
    s w = false ->
    t w = false.
Proof.
  intros s t w H1 H2.
  destruct (t w) eqn:H3; try reflexivity.
  apply H1 in H3.
  congruence.
Qed.

(**
   We will now see, that [substate] is a [PreOrder].
 *)
Print PreOrder.
(**
   A [PreOrder] is a [reflexive] and [transitive] [relation],
   at least, if we follow the way, Coq defines it as such.
 *)
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

(**
   We can also prove that [state_eq] is a congruence relation
   with respect to [substate]:
 *)
Instance substate_Proper `{Model} : Proper (state_eq ==> state_eq ==> iff) substate.
Proof.
  intros s1 s2 H1 t1 t2 H2.
  split.
  -
    intros H3 w H4.
    rewrite <- H2.
    apply H3.
    rewrite H1.
    exact H4.
  -
    intros H3 w H4.
    rewrite H2.
    apply H3.
    rewrite <- H1.
    exact H4.
Qed.

Lemma substate_empty_state `{Model} :
  forall t,
    substate t empty_state ->
    state_eq t empty_state.
Proof.
  intros t H1 w.
  destruct (t w) eqn:H2; try reflexivity.
  apply H1 in H2.
  discriminate.
Qed.

Lemma substate_singleton `{Model} :
  forall w t,
    substate t (singleton w) ->
    (
      state_eq t empty_state \/
      state_eq t (singleton w)
    ).
Proof.
  intros w t H1.
  destruct (t w) eqn:H2.
  -
    right.
    intros w'.
    destruct (t w') eqn:H3.
    +
      symmetry.
      apply H1.
      exact H3.
    +
      symmetry.
      apply singleton_false.
      intros H4.
      rewrite H4 in H3.
      congruence.
  -
    left.
    intros w'.
    destruct (t w') eqn:H3; try reflexivity.
    apply H1 in H3 as H4.
    apply singleton_true in H4.
    rewrite H4 in H3.
    congruence.
Qed.

Lemma singleton_substate `{Model} :
  forall (s : state) w,
    s w = true ->
    substate (singleton w) s.
Proof.
  intros s w H1 w' H2.
  apply singleton_true in H2.
  rewrite H2.
  exact H1.
Qed.

Lemma substate_complement `{Model} :
  forall s t,
    substate t s <->
    substate (complement s) (complement t).
Proof.
  intros s t.
  split.
  all: intros H1 w H2.
  -
    apply complement_true.
    apply complement_true in H2.
    eapply substate_contrapos.
    all: eassumption.
  -
    apply complement_false.
    apply complement_false in H2.
    eapply substate_contrapos.
    all: eassumption.
Qed.

Lemma substate_excluding_state `{Model} :
  forall s w,
    substate (excluding_state s w) s.
Proof.
  intros s w w' H1.
  simpl in H1.
  destruct (w == w') as [H2|H2]; easy.
Qed.

Instance mapping_state_Proper_substate `{Model} :
  Proper (Morph_eq ==> InS_sublist ==> substate) mapping_state.
Proof.
  intros f1 f2 H1 ns1 ns2 H2 w H3.
  apply InS_iff_inbS_true.
  apply InS_iff_inbS_true in H3.
  apply InS_map_E in H3 as [n [H3 H4]].
  red in H1.
  rewrite H1 in H3.
  rewrite <- H3.
  apply InS_map_I.
  apply H2.
  exact H4.
Qed.

Lemma unnamed_helper_States_2 `{Model} :
  forall t f n ns,
    substate t (mapping_state f (n :: ns)) ->
    substate (excluding_state t (f n)) (mapping_state f ns).
Proof.
  intros t f n ns H1 w H2.
  simpl in H2.
  destruct ((f n) == w) as [H3|H3].
  -
    discriminate.
  -
    apply H1 in H2 as H4.
    apply InS_iff_inbS_true.
    apply InS_iff_inbS_true in H4.
    simpl in H4.
    apply InS_cons_E in H4 as [H4|H4].
    +
      symmetry in H4.
      contradiction.
    +
      exact H4.
Qed.

Lemma substate_mapping_state_iff `{Model} :
  forall f ns t,
  substate t (mapping_state f ns) <->
  exists ns',
    state_eq t (mapping_state f ns') /\
    InS_sublist ns' ns.
Proof.
  intros f ns1 t.
  split.
  -
    intros H1.
    generalize dependent t.
    induction ns1 as [|n ns1' IH].
    all: intros t H1.
    +
      exists nil.
      split.
      *
        rewrite mapping_state_nil in H1.
        apply substate_empty_state in H1.
        rewrite H1, mapping_state_nil.
        reflexivity.
      *
        easy.
    +
      destruct (t (f n)) eqn:H2.
      *
        specialize IH with
          (t := excluding_state t (f n)).
        destruct IH as [ns' [H3 H4]].
        {
          apply unnamed_helper_States_2.
          exact H1.
        }
        exists (n :: ns').
        split.
        --
           intros w.
           rewrite mapping_state_cons.
           rewrite <- H3.
           unfold excluding_state.
           simpl.
           unfold "_ ==b _".
           destruct (w == f n) as [H5|H5].
           ++
              simpl.
              rewrite H5.
              exact H2.
           ++
              simpl.
              destruct (f n == w) as [H6|H6].
              **
                 symmetry in H6; contradiction.
              **
                 reflexivity.
        --
           intros n' H5.
           apply InS_cons_E in H5 as [H5|H5].
           ++
              apply InS_cons_I_hd.
              exact H5.
           ++
              apply InS_cons_I_tl.
              apply H4.
              exact H5.
      *
        specialize IH with
          (t := t).
        destruct IH as [ns' [H3 H4]].
        {
          intros w H3.
          apply H1 in H3 as H4.
          apply InS_iff_inbS_true in H4.
          simpl in H4.
          apply InS_cons_E in H4 as [H4|H4].
          -
            rewrite H4 in H3.
            congruence.
          -
            apply InS_iff_inbS_true.
            exact H4.
        }
        exists ns'.
        split.
        --
           exact H3.
        --
           apply InS_sublist_cons_I.
           exact H4.
  -
    intros [ns2 [H1 H2]].
    rewrite H1, H2.
    reflexivity.
Qed.

Program Definition restricted_Model `{M : Model} (s : state) : Model :=
  {|
    World := {w : World | s w = true};
    World_Setoid :=
      {|
        equiv := fun x y => (proj1_sig x == proj1_sig y)%type
      |};
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
  constructor.
  -
    intros x.
    reflexivity.
  -
    intros x y H1.
    symmetry. exact H1.
  -
    intros x y z H1 H2.
    rewrite H1.
    exact H2.
Qed.

Next Obligation.
  intros x y.
  simpl.
  apply equiv_dec.
Qed.

Next Obligation.
  repeat intro.
  apply PInterpretation_Proper.
  assumption.
Qed.

Next Obligation.
  repeat intro.
  apply FInterpretation_Proper.
  assumption.
Qed.

Next Obligation.
  apply rigidity.
  assumption.
Qed.

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
  simpl.
  rewrite H1.
  reflexivity.
Qed.

Definition unrestricted_state
  `{Model}
  (s : state)
  (t : @state _ (restricted_Model s)) : state.
Proof.
  unshelve econstructor.
  -
    intros w.
    destruct (s w) eqn:H1.
    +
      exact (t (exist _ _ H1)).
    +
      exact false.
  -
    intros w1 w2 H1.
    simpl.
    set (f :=
      (
        fun (b' : bool) (w : World) =>
        (
          if b' as b return (s w = b -> bool)
          then fun H2 : s w = true =>
            t (exist (fun w : World => s w = true) w H2)
          else fun _ : s w = false =>
            false
        )
      )
    ).
    assert (H42 :
      forall b1 b2 w1 w2 (H1 : s w1 = b1) (H2 : s w2 = b2),
        b1 = b2 ->
        w1 == w2 ->
        f b1 w1 H1 = f b2 w2 H2
    ).
    {
      clear dependent w1.
      clear dependent w2.
      intros b1 b2 w1 w2 H1 H2 H3 H4.
      destruct b1, b2; try congruence.
      -
        apply (@morph_Proper _ _ World_Setoid (eq_setoid bool)).
        exact H4.
      -
        reflexivity.
    }
    apply H42.
    +
      rewrite H1.
      reflexivity.
    +
      exact H1.
Defined.

Lemma unnamed_States_helper_1 `{Model} :
  forall (s t : state) w,
    s w = false ->
    unrestricted_state s t w = false.
Proof.
  intros s t w H1.
  unfold unrestricted_state.
  simpl.
  set (f :=
    (
      fun (b' : bool) (w : World) =>
      (
        if b' as b return (s w = b -> bool)
        then fun H2 : s w = true =>
          t (exist (fun w : World => s w = true) w H2)
        else fun _ : s w = false =>
          false
      )
    )
  ).
  assert (H42 :
    forall b w H1,
      b = false ->
      f b w H1 = false
  ).
  {
    clear dependent w.
    intros b w H1 H2.
    unfold f.
    destruct b; easy.
  }
  eapply H42.
  exact H1.
Qed.

Lemma unnamed_States_helper_2 `{Model} :
  forall (s t : state) w (H1 : s w = true),
    unrestricted_state s t w = t (exist _ _ H1).
Proof.
  intros s t w H1.
  simpl.
  set (f :=
    (
      fun (b' : bool) (w : World) =>
      (
        if b' as b return (s w = b -> bool)
        then fun H2 : s w = true =>
          t (exist (fun w : World => s w = true) w H2)
        else fun _ : s w = false =>
          false
      )
    )
  ).
  assert (H42 :
    forall b w (H1 : s w = b) (H2 : s w = true),
      f b w H1 = t (exist _ w H2)
  ).
  {
    clear dependent w.
    intros b w H1 H2.
    destruct b.
    -
      apply (@morph_Proper _ _ World_Setoid (eq_setoid bool)).
      simpl.
      reflexivity.
    -
      congruence.
  }
  apply H42.
Qed.

Lemma unrestricted_substate `{Model} :
  forall s1 s2 s3,
    substate s3 (restricted_state s1 s2) ->
    substate (unrestricted_state s1 s3) s2.
Proof.
  intros * H1 w H2.
  (*
  enough (H3 : s1 w && s2 w = true).
  {
    apply andb_true_iff in H3 as [H3 H4].
    exact H4.
  }
   *)
  destruct (s1 w) eqn:H3.
  -
    rewrite unnamed_States_helper_2 with (H1 := H3) in H2.
    apply H1 in H2.
    apply andb_true_iff in H2 as [H21 H22].
    exact H22.
  -
    rewrite unnamed_States_helper_1 in H2; easy.
Qed.

Lemma unnamed_States_helper_3 `{Model}:
  forall s t,
    state_eq t (restricted_state s (unrestricted_state s t)).
Proof.
  intros s t [w H1].
  symmetry.
  simpl.
  rewrite H1 at 1.
  simpl.
  apply unnamed_States_helper_2.
Qed.
