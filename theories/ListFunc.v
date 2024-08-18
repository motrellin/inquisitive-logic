From Coq Require Export List.

Definition list_func {X Y} : list X -> list Y -> list (list (X*Y)) :=
  list_rect
  _
  (fun ys => nil :: nil)
  (fun x xs' R =>
    list_rect
    _
    nil
    (fun y ys' _ =>
      flat_map
      (
        fun xys =>
        map (fun y => (x,y) :: xys) (y :: ys')
      )
      (R (y :: ys'))
    )
  ).

Compute (list_func (1 :: 2 :: nil) (3 :: 4 :: nil)).
Compute length (list_func (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)).

Theorem list_func_left_total {X Y} :
  forall (xs : list X) (ys : list Y) xys,
    In xys (list_func xs ys) ->
    forall x,
      In x xs ->
      exists y,
        In y ys /\
        In (x,y) xys.
Proof.
  induction xs as [|x1 xs' IH].
  all: intros ys xys H1 x2 H3.
  -
    contradiction.
  -
    destruct ys as [|y1 ys'].
    +
      contradiction.
    +
      specialize (IH (y1 :: ys')).
      simpl in *.
      apply in_flat_map in H1.
      destruct H1 as [xys' [H1 H2]].
      simpl in *.
      destruct H2 as [H2|H2], H3 as [H3|H3].
      *
        subst x2 xys.
        simpl in *.
        exists y1; firstorder.
      *
        subst xys.
        specialize (IH xys' H1 x2 H3).
        destruct IH as [y2 [H4 H5]].
        destruct H4 as [H4|H4].
        --
           subst y2.
           simpl in *.
           firstorder.
        --
           firstorder.
      *
        subst x2.
        simpl in *.
        specialize (IH xys' H1).
        apply in_map_iff in H2 as [y2 [H2 H3]].
        subst xys.
        simpl in *.
        firstorder.
      *
        specialize (IH xys' H1 x2 H3).
        destruct IH as [y2 [H4 H5]].
        simpl in *.
        apply in_map_iff in H2 as [y3 [H6 H7]].
        subst.
        firstorder.
Qed.

Theorem list_func_in {X Y} :
  forall (xs : list X) (ys : list Y) xys,
    In xys (list_func xs ys) ->
    forall x y,
      In (x,y) xys ->
      In x xs /\
      In y ys.
Proof.
  induction xs as [|x xs' IH].
  all: intros ys xys H1 x1 y1 H2.
  -
    simpl in *.
    destruct H1 as [H1|H1].
    +
      subst xys.
      contradiction.
    +
      contradiction.
  -
    destruct ys as [|y ys'].
    +
      contradiction.
    +
      simpl in *.
      apply in_flat_map in H1 as [xys' [H11 H12]].
      simpl in *.
      destruct H12 as [H12|H12].
      *
        subst xys.
        specialize (IH (y :: ys') xys' H11 x1 y1).
        simpl in H2.
        destruct H2 as [H2|H2].
        --
           injection H2; intros H3 H4; subst x1 y1; clear H2.
           firstorder.
        --
           firstorder.
      *
        apply in_map_iff in H12 as [y2 [H12 H13]].
        subst xys.
        specialize (IH (y :: ys') xys' H11).
        simpl in H2.
        destruct H2 as [H2|H2].
        --
           injection H2; intros H3 H4; subst x1 y1; clear H2.
           firstorder.
        --
           firstorder.
Qed.

Definition unique {X} : list X -> Prop :=
  list_rect
  _
  True
  (fun x xs' R => (~ In x xs') /\ R).

Theorem list_func_right_unique {X Y} :
  forall (xs : list X) (ys : list Y),
    unique xs ->
    forall xys,
      In xys (list_func xs ys) ->
      forall x y1 y2,
        In (x,y1) xys ->
        In (x,y2) xys ->
        y1 = y2.
Proof.
  induction xs as [|x xs' IH].
  all: intros ys H1 xys H2 x' y1 y2 H3 H4.
  -
    simpl in *.
    destruct H2 as [H2|H2].
    +
      subst xys.
      contradiction.
    +
      contradiction.
  -
    simpl in *.
    destruct H1 as [H11 H12].
    destruct ys as [|y ys'].
    +
      simpl in *.
      contradiction.
    +
      simpl in *.
      apply in_flat_map in H2 as [xys' [H21 H22]].
      simpl in *.
      destruct H22 as [H22|H22].
      *
        subst xys.
        simpl in *.
        destruct H3 as [H3|H3].
        --
           injection H3; intros; subst x' y1; clear H3.
           simpl in *.
           destruct H4 as [H4|H4].
           ++
              injection H4; intros; subst y2; clear H4.
              reflexivity.
           ++
              eapply list_func_in in H4 as [H4 H5].
              contradict H11.
              exact H4.
              exact H21.
        --
           destruct H4 as [H4|H4].
           ++
              injection H4; intros; subst x' y2; clear H4.
              eapply list_func_in in H3 as [H3 H4].
              contradict H11.
              exact H3.
              exact H21.
           ++
              eapply IH.
              exact H12.
              exact H21.
              exact H3.
              exact H4.
      *
        apply in_map_iff in H22 as [y3 [H22 H23]].
        subst xys.
        simpl in *.
        destruct H3 as [H3|H3].
        --
           injection H3; intros; subst x' y1; clear H3.
           simpl in *.
           destruct H4 as [H4|H4].
           ++
              injection H4; intros; subst y2; clear H4.
              reflexivity.
           ++
              eapply list_func_in in H4 as [H4 H5].
              contradict H11.
              exact H4.
              exact H21.
        --
           destruct H4 as [H4|H4].
           ++
              injection H4; intros; subst x' y2; clear H4.
              eapply list_func_in in H3 as [H3 H4].
              contradict H11.
              exact H3.
              exact H21.
           ++
              eapply IH.
              exact H12.
              exact H21.
              exact H3.
              exact H4.
Qed.
