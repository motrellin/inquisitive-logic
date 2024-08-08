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
      flat_map (fun xys => map (fun y => (x,y) :: xys) (y :: ys')) (R (y :: ys'))
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
