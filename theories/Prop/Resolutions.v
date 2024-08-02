From Coq Require Export List.
From InqLog.Prop Require Export LP.

Definition list_func {X Y} : list X -> list Y -> list (list (X*Y)) :=
  list_rect
  _
  (fun ys => nil) (* Base Case *)
  (fun x xs' r1 => (* Recursive Case *)
    list_rect
    _
    (map (fun y => (x,y) :: nil))
    (fun _ _ _ ys =>
      flat_map
      (
        fun f =>
        map
        (
          fun y =>
          (x,y) :: f
        )
        ys
      )
      (r1 ys)
    )
    xs'
  ).

Compute (list_func (1 :: 2 :: nil) (3 :: 4 :: nil)).
Compute length (list_func (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)).

Definition resolution : form -> list form :=
  form_rec
  _
  (fun a => (atom a) :: nil)
  (bot :: nil)
  (fun f1 r1 f2 r2 => flat_map (fun x => map (fun y => conj x y) r2) r1)
  (fun f1 r1 f2 r2 =>
    map
    (
      fun f =>
      list_rect
      _
      top
      (fun x _ rest => conj (impl (fst x) (snd x)) rest)
      f
    )
    (list_func r1 r2)
  )
  (fun f1 r1 f2 r2 => r1 ++ r2).

Compute (resolution (iquest (atom 0))).
Compute (resolution (impl (iquest (atom 0)) (iquest (atom 1)))).

Theorem thm_3_6_7 `{Model} :
  forall f s,
    s |= f <->
    exists r,
      s |= r /\
      In r (resolution f).
Proof.
  induction f as [a| |f1 IH1 f2 IH2|f1 IH1 f2 IH2|f1 IH1 f2 IH2].
  all: intros s.
  -
    split.
    +
      intros H1.
      exists (atom a).
      split.
      *
        exact H1.
      *
        left.
        reflexivity.
    +
      intros [r [H1 H2]].
      destruct H2 as [H2|H2].
      *
        subst; exact H1.
      *
        contradiction.
  -
    split.
    +
      intros H1.
      exists bot.
      split.
      *
        exact H1.
      *
        left.
        reflexivity.
    +
      intros [r [H1 H2]].
      destruct H2 as [H2|H2].
      *
        subst; exact H1.
      *
        contradiction.
  -
    split.
    +
      intros [H1 H4].
      apply IH1 in H1 as [r1 [H2 H3]].
      apply IH2 in H4 as [r2 [H5 H6]].
      exists (conj r1 r2).
      split.
      *
        split; assumption.
      *
        simpl in *.
        apply in_flat_map.
        exists r1.
        split.
        --
           exact  H3.
        --
           apply in_map_iff.
           exists r2.
           split.
           ++
              reflexivity.
           ++
              exact H6.
    +
      intros [r [H1 H2]].
      simpl in H2.
      apply in_flat_map in H2 as [r1 [H3 H4]].
      apply in_map_iff in H4 as [r2 [H5 H6]].
      subst r.
      destruct H1 as [H11 H12].
      split.
      *
        apply IH1.
        exists r1.
        split; assumption.
      *
        apply IH2.
        exists r2.
        split; assumption.
  -
    split.
    +
      intros H1.
      assert (H2 : forall r1, In r1 (resolution f1) -> exists r2, In r2 (resolution f2) /\ s |= impl r1 r2).
      {
        intros r1 H2.
        remember (intersection_state s (truth_set r1)) as cap eqn:H3.
        assert (H4 : cap |= r1).
        {
          (* TODO
             Proof Sketch:
             - Since [r1] is a resolution, it must be truth-conditional.
             - A truth-conditional formula should be satisfied at any substate of its truth set.
           *)
          admit.
        }
        assert (H5 : cap |= f1).
        {
          apply IH1.
          exists r1.
          split; assumption.
        }
        assert (H6 : cap |= f2).
        {
          simpl in H1.
          apply H1.
          -
            admit.
          -
            exact H5.
        }
        apply IH2 in H6 as [r2 [H6 H7]].
        exists r2.
        split.
        -
          exact H7.
        -
          (* TODO Use Prop 2.5.2 *)
          admit.
      }
      assert (H3 :
        exists (f : {r1 : form | In r1 (resolution f1)} -> {r2 : form | In r2 (resolution f2)}),
          forall x,
            s |= impl (proj1_sig x) (proj1_sig (f x))).
      {
        (* TODO Some Coq specific stuff *)
        admit.
      }
      destruct H3 as [f H3].
      (* TODO More Coq Stuff *)
      admit.
    +
      intros [r [H1 H2]].
      simpl in H2.
      apply in_map_iff in H2 as [ffs [H2 H3]].
      intros t H4 H5.
      apply IH1 in H5 as [r1 [H5 H6]].
      assert (H7 : exists r2, In (r1,r2) ffs).
      {
        (* TODO This holds, as ffs represents a funktion. In fact, Coq stuff *)
        admit.
      }
      destruct H7 as [r2 H7].
      assert (H8 : s |= impl r1 r2).
      {
        (* TODO Coq stuff *)
        admit.
      }
      assert (H9 : t |= r2).
      {
        simpl in H8.
        apply H8.
        -
          exact H4.
        -
          exact H5.
      }
      apply IH2.
      exists r2.
      split.
      *
        exact H9.
      *
        (* TODO This should follow by the definition of ffs. *)
        admit.
  -
    split.
    +
      intros [H1|H1].
      *
        apply IH1 in H1 as [r [H2 H3]].
        exists r.
        split.
        --
           exact H2.
        --
           simpl.
           apply in_app_iff.
           left.
           exact H3.
      *
        apply IH2 in H1 as [r [H2 H3]].
        exists r.
        split.
        --
           exact H2.
        --
           simpl.
           apply in_app_iff.
           right.
           exact H3.
    +
      intros [r [H1 H2]].
      simpl in H2.
      apply in_app_iff in H2.
      destruct H2 as [H2|H2].
      *
        left.
        apply IH1.
        exists r.
        split; assumption.
      *
        right.
        apply IH2.
        exists r.
        split; assumption.
Admitted.
