From Coq Require Export
  Bool
  List
  Lia
  SetoidList.

From InqLog Require Export SetoidLib.

Generalizable Variables X Y.

Definition InS `{Setoid X} := InA equiv.

Lemma InS_nil `{Setoid X} :
  forall x,
    ~ InS x nil.
Proof.
  inversion 1.
Qed.

Lemma InS_cons `{Setoid X} :
  forall x x' xs,
    InS x (x' :: xs) ->
    x == x' \/
    InS x xs.
Proof.
  inversion 1; firstorder.
Qed.

Definition inbS `{EqDec X} (x : X) : list X -> bool :=
  existsb (equiv_decb x).

Lemma InS_reflect_inbS `{EqDec X} :
  forall x xs,
  reflect (InS x xs) (inbS x xs).
Proof.
  induction xs as [|x' xs' IH].
  -
    right.
    inversion 1.
  -
    simpl.
    destruct IH as [IH|IH].
    +
      rewrite orb_true_r.
      left.
      right.
      exact IH.
    +
      rewrite orb_false_r.
      unfold "_ ==b _".
      destruct (x == x') as [H1|H1].
      *
        left.
        left.
        exact H1.
      *
        right.
        intros H2.
        apply InA_cons in H2 as [H2|H2]; contradiction.
Qed.

Proposition InS_dec `{EqDec X} :
  forall x xs,
    {InS x xs} + {~ InS x xs}.
Proof.
  intros x xs.
  eapply reflect_dec.
  apply InS_reflect_inbS.
Qed.

Corollary InS_iff_inbS_true `{EqDec X} :
  forall x xs,
    InS x xs <->
    inbS x xs = true.
Proof.
  intros x xs.
  apply reflect_iff.
  apply InS_reflect_inbS.
Qed.

Corollary InS_iff_inbS_false `{EqDec X} :
  forall x xs,
    (~ InS x xs) <->
    inbS x xs = false.
Proof.
  intros x xs.
  split.
  -
    intros H1.
    destruct (inbS x xs) eqn:H2; try reflexivity.
    apply InS_iff_inbS_true in H2.
    contradiction.
  -
    intros H1 H2.
    apply InS_iff_inbS_true in H2.
    congruence.
Qed.

Corollary InS_iff_inbS `{EqDec X} :
  forall x xs y ys,
    (InS x xs <-> InS y ys) <->
    inbS x xs =
    inbS y ys.
Proof.
  intros x xs y ys.
  split.
  -
    intros H1.
    destruct (inbS y ys) eqn:H2.
    +
      apply InS_iff_inbS_true.
      apply H1.
      apply InS_iff_inbS_true.
      exact H2.
    +
      apply InS_iff_inbS_false.
      intros H3.
      apply H1 in H3.
      apply InS_iff_inbS_true in H3.
      congruence.
  -
    intros H1.
    split.
    all: intros H2.
    all: apply InS_iff_inbS_true.
    +
      rewrite <- H1.
      apply InS_iff_inbS_true.
      exact H2.
    +
      rewrite H1.
      apply InS_iff_inbS_true.
      exact H2.
Qed.

Definition InS_sublist `{Setoid X} : relation (list X) :=
  fun xs1 xs2 =>
  forall x,
    InS x xs1 ->
    InS x xs2.

Lemma InS_sublist_nil `{Setoid X} :
  forall (xs : list X),
    InS_sublist xs nil ->
    xs = nil.
Proof.
  intros [|x xs'] H1.
  all: try reflexivity.
  exfalso.
  eapply InS_nil.
  apply H1.
  left.
  reflexivity.
Qed.

Instance InS_sublist_PreOrder `{Setoid X} :
  PreOrder InS_sublist.
Proof.
  split.
  -
    intros xs x H1.
    exact H1.
  -
    intros xs1 xs2 xs3 H1 H2 x H3.
    apply H2.
    apply H1.
    exact H3.
Qed.

Lemma cons_In_sublist_cons `{Setoid X} :
  forall (x : X) xs1 xs2,
    InS_sublist xs1 xs2 ->
    InS_sublist (x :: xs1) (x :: xs2).
Proof.
  intros x1 xs1 xs2 H1 x2 H2.
  apply InS_cons in H2 as [H2|H2].
  -
    left.
    exact H2.
  -
    right.
    apply H1.
    exact H2.
Qed.

Lemma InS_map `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y) (xs : list X) (x : X),
    InS x xs ->
    InS (f x) (map f xs).
Proof.
  induction xs as [|x1 xs' IH].
  all: intros x H1.
  -
    contradict H1.
    apply InS_nil.
  -
    apply InS_cons in H1 as [H1|H1].
    +
      left.
      rewrite H1.
      reflexivity.
    +
      simpl.
      right.
      apply IH; assumption.
Qed.

Lemma InS_map_iff `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y) (xs : list X) (y : Y),
    InS y (map f xs) <->
    exists x,
      f x == y /\
      InS x xs.
Proof.
  intros f xs y.
  split.
  -
    intros H1.
    induction xs as [|x xs' IH].
    +
      contradict H1; apply InS_nil.
    +
      simpl in H1.
      apply InS_cons in H1 as [H1|H1].
      *
        exists x.
        split.
        --
           symmetry.
           exact H1.
        --
           left; reflexivity.
      *
        specialize (IH H1).
        destruct IH as [x' [H2 H3]].
        exists x'.
        split.
        --
           exact H2.
        --
           right.
           exact H3.
  -
    intros [x [H1 H2]].
    rewrite <- H1.
    apply InS_map; assumption.
Qed.

Lemma map_In_sublist_map `(f : Morph X Y) :
  forall xs1 xs2,
    InS_sublist xs1 xs2 ->
    InS_sublist (map f xs1) (map f xs2).
Proof.
  intros xs1 xs2 H1 y H2.
  apply InS_map_iff in H2 as [x [H2 H3]].
  rewrite <- H2.
  apply InS_map.
  apply H1.
  exact H3.
Qed.

Lemma In_sublist_dec {X} `{EqDec X} :
  forall (xs1 xs2 : list X),
    {InS_sublist xs1 xs2} +
    {exists x, InS x xs1 /\ ~ InS x xs2}.
Proof.
  intros xs1 xs2.
  induction xs1 as [|x xs1' [IH|IH]].
  -
    left.
    easy.
  -
    simpl.
    destruct (InS_dec x xs2) as [H2|H2].
    +
      left.
      intros x' H3.
      apply InS_cons in H3 as [H3|H3].
      *
        rewrite H3.
        exact H2.
      *
        apply IH.
        exact H3.
    +
      right.
      exists x.
      split.
      *
        left.
        reflexivity.
      *
        exact H2.
  -
    right.
    destruct IH as [x' [H2 H3]].
    exists x'.
    split.
    +
      right.
      exact H2.
    +
      exact H3.
Qed.

Definition InS_eq `{Setoid X} : relation (list X) :=
  fun ls rs =>
  InS_sublist ls rs /\
  InS_sublist rs ls.

Instance InS_eq_equiv `{Setoid X} : Equivalence InS_eq.
Proof.
  firstorder.
Qed.

Lemma InS_eq_nil `{Setoid X} :
  forall (xs : list X),
    InS_eq xs nil ->
    xs = nil.
Proof.
  destruct xs as [|x xs'].
  -
    reflexivity.
  -
    intros [H1 H2].
    apply InS_sublist_nil.
    exact H1.
Qed.

Instance cons_Proper `{Setoid X} :
  Proper (equiv ==> InS_eq ==> InS_eq) cons.
Proof.
  intros x1 x2 H1 xs1 xs2 H2.
  split.
  all: intros x3 H3.
  all: apply InS_cons in H3 as [H3|H3].
  -
    left.
    rewrite H3.
    exact H1.
  -
    right.
    apply H2.
    exact H3.
  -
    left.
    rewrite H1.
    exact H3.
  -
    right.
    apply H2.
    exact H3.
Qed.

Lemma InS_sublist_singleton `{EqDec X} :
  forall x (xs : list X),
    InS_sublist xs (x :: nil) ->
    xs = nil \/
    InS_eq xs (x :: nil).
Proof.
  intros x xs H1.
  destruct (InS_dec x xs) as [H2|H2].
  -
    right.
    split; try assumption.
    intros x' H3.
    apply InS_cons in H3 as [H3|H3].
    +
      rewrite H3.
      exact H2.
    +
      contradict H3.
      apply InS_nil.
  -
    left.
    destruct xs as [|x' xs']; try reflexivity.
    exfalso.
    assert (H3 : x =/= x') by (intros H3; apply H2; left; exact H3).
    assert (H4 : InS x' (x :: nil)) by (apply H1; left; reflexivity).
    apply InS_cons in H4 as [H4|H4].
    +
      symmetry in H4; contradiction.
    +
      eapply InS_nil; exact H4.
Qed.

Lemma In_eq_cons_cons `{Setoid X} :
  forall (x1 x2 : X) xs,
    InS_eq (x1 :: x2 :: xs) (x2 :: x1 :: xs).
Proof.
  intros *.
  split.
  all: intros x H1.
  all: apply InS_cons in H1 as [H1|H1].
  all: try apply InS_cons in H1 as [H1|H1].
  all: (left + (right; left + right); exact H1).
Qed.

Lemma InS_app_iff `{Setoid X} :
  forall xs1 xs2 x,
    InS x (xs1 ++ xs2) <->
    InS x xs1 \/ InS x xs2.
Proof.
  induction xs1 as [|x1 xs1' IH].
  all: intros xs2 x.
  -
    split.
    +
      intros H1.
      right.
      exact H1.
    +
      intros [H1|H1]; easy.
  -
    simpl.
    split.
    +
      intros H1.
      apply InS_cons in H1 as [H1|H1].
      left.
      left.
      exact H1.
      apply IH in H1 as [H1|H1].
      *
        left.
        right.
        exact H1.
      *
        right.
        exact H1.
    +
      intros [H1|H1].
      *
        apply InS_cons in H1 as [H1|H1].
        --
           left.
           exact H1.
        --
           right.
           apply IH.
           left.
           exact H1.
      *
        right.
        apply IH.
        right.
        exact H1.
Qed.

Instance app_Proper `{Setoid X} :
  Proper (InS_eq ==> InS_eq ==> InS_eq) (@app X).
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  split.
  all: intros x H3.
  all: apply InS_app_iff.
  all: apply InS_app_iff in H3 as [H3|H3].
  all: apply H1 in H3 + apply H2 in H3.
  all: left + right; exact H3.
Qed.

Lemma In_eq_app_comm `{Setoid X} :
  forall (xs1 xs2 : list X),
    InS_eq (xs1 ++ xs2) (xs2 ++ xs1).
Proof.
  intros xs1 xs2.
  split.
  all: intros x H1.
  all: apply InS_app_iff.
  all: apply InS_app_iff in H1 as [H1|H1].
  all: left + right; exact H1.
Qed.

Lemma In_Sublist_singleton `{EqDec X} :
  forall (xs : list X) (x : X),
    InS_sublist xs (x :: nil) ->
    InS_eq xs (x :: nil) \/
    xs = nil.
Proof.
  intros xs x1 H1.
  destruct (InS_dec x1 xs) as [H2|H2].
  -
    left.
    split.
    +
      auto.
    +
      intros x2 H3.
      apply InS_cons in H3 as [H3|H3].
      *
        rewrite H3.
        exact H2.
      *
        exfalso.
        eapply InS_nil.
        exact H3.
  -
    right.
    destruct xs as [|x2 xs'].
    +
      reflexivity.
    +
      exfalso.
      assert (H3 : InS x2 (x2 :: xs')). left; reflexivity.
      apply H1 in H3 as H4.
      apply InS_cons in H4 as [H4|H4].
      *
        rewrite H4 in H3 at 1.
        contradiction.
      *
        eapply InS_nil.
        exact H4.
Qed.

Definition length_order {X} : relation (@list X) :=
  fun xs1 xs2 =>
  length xs1 < length xs2.

Proposition length_order_wf {X} :
  well_founded (@length_order X).
Proof.
  red.
  assert (H1 :
    forall s (xs : list X),
      length xs <= s -> Acc length_order xs
  ).
  {
    induction s as [|s' IH].
    all: intros xs1 H1.
    all: constructor.
    all: intros xs2 H2.
    all: red in H2.
    all: try apply IH.
    all: lia.
  }
  intros xs.
  eapply H1.
  reflexivity.
Qed.

Definition InS_sublist_order `{Setoid X} : relation (@list X) :=
  fun xs1 xs2 =>
  InS_sublist xs1 xs2 /\
  exists x,
    InS x xs2 /\
    ~ InS x xs1.

Proposition InS_sublist_order_wf `{EqDec X} :
  well_founded InS_sublist_order.
Proof.
  red.
  assert (H2 :
    forall (xs1 xs2 : list X),
      InS_sublist xs2 xs1 ->
      Acc InS_sublist_order xs2
  ).
  {
    induction xs1 as [xs1 IH] using (well_founded_ind length_order_wf).
    intros xs2 H2.
    constructor.
    intros xs3 [H3 H4].
    destruct H4 as [x1 [H4 H5]].
    eapply IH with
      (y := filter (nequiv_decb x1) xs1).
    -
      apply H2 in H4 as H6.
      clear dependent xs3.
      clear dependent xs2.
      clear IH.
      rename H6 into H2.
      induction xs1 as [|x2 xs1' IH].
      +
        easy.
      +
        unfold length_order in *.
        unfold "_ <>b _" in *.
        unfold "_ ==b _" in *.
        simpl in *.
        apply InS_cons in H2 as [H2|H2].
        *
          destruct (InS_dec x1 xs1') as [H3|H3].
          --
             specialize (IH H3).
             destruct (x1 == x2) as [_|H4]; try contradiction.
             simpl.
             lia.
          --
             clear IH.
             destruct (x1 == x2) as [_|H4]; try contradiction.
             simpl.
             assert (H4 :
              filter
              (fun y : X => negb (if x1 == y then true else false))
              xs1' =
              xs1'
            ).
            {
              clear dependent x2.
              rename xs1' into xs1.
              induction xs1 as [|x2 xs1' IH].
              -
                reflexivity.
              -
                simpl.
                destruct (x1 == x2) as [H4|H4].
                +
                  simpl.
                  exfalso.
                  apply H3.
                  left.
                  exact H4.
                +
                  simpl.
                  f_equal.
                  apply IH.
                  intros H5.
                  apply H3.
                  right.
                  exact H5.
            }
            rewrite H4.
            lia.
        *
          specialize (IH H2).
          destruct (x1 == x2) as [H3|H3].
          --
             simpl.
             lia.
          --
             simpl.
             lia.
    -
      intros x2 H6.
      apply filter_InA.
      {
        intros x3 x4 H7.
        unfold "_ <>b _".
        unfold "_ ==b _".
        destruct (x1 == x3) as [H8|H8].
        all: destruct (x1 == x4) as [H9|H9].
        all: reflexivity + rewrite H7 in H8; contradiction.
      }
      split.
      +
        apply H2.
        apply H3.
        exact H6.
      +
        unfold "_ <>b _".
        unfold "_ ==b _".
        destruct (x1 == x2) as [H7|H7].
        *
          rewrite H7 in H5.
          contradiction.
        *
          reflexivity.
  }
  intros xs.
  eapply H2.
  reflexivity.
Qed.

Lemma cons_InS_sublist_cons `{EqDec X} :
  forall x xs1 xs2,
    InS_sublist xs1 xs2 ->
    InS_sublist (x :: xs1) (x :: xs2).
Proof.
  intros x1 xs1 xs2 H1 x2 H2.
  apply InS_cons in H2 as [H2|H2].
  -
    left.
    exact H2.
  -
    right.
    apply H1.
    exact H2.
Qed.

Lemma map_InS_sublist_map `{EqDec X} `{EqDec Y} :
  forall (f : Morph X Y) xs1 xs2,
    InS_sublist xs1 xs2 ->
    InS_sublist (map f xs1) (map f xs2).
Proof.
  intros f xs1 xs2 H1 y H2.
  apply InS_map_iff in H2 as [x [H2 H3]].
  rewrite <- H2.
  apply InS_map.
  apply H1.
  exact H3.
Qed.
