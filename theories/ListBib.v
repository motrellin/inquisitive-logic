From InqLog Require Export SetoidLib.

Generalizable Variables X Y.

(** * [InS] *)

Definition InS `{Setoid X} := InA equiv.

(** ** [nil] *)

Fact InS_nil_E `{Setoid X} :
  forall x,
    ~ InS x nil.
Proof.
  inversion 1.
Qed.

(** ** [cons] *)

Fact InS_cons_I_hd `{Setoid X} :
  forall x x' xs,
    x == x' ->
    InS x (x' :: xs).
Proof.
  intros * H1.
  left.
  exact H1.
Qed.

Fact InS_cons_I_tl `{Setoid X} :
  forall x x' xs,
    InS x xs ->
    InS x (x' :: xs).
Proof.
  intros * H1.
  right.
  exact H1.
Qed.

Fact InS_cons_E `{Setoid X} :
  forall x x' xs,
    InS x (x' :: xs) ->
    x == x' \/
    InS x xs.
Proof.
  inversion 1; firstorder.
Qed.

(** ** [app] **)

Lemma InS_app_I_1 `{Setoid X} :
  forall x xs1 xs2,
    InS x xs1 ->
    InS x (xs1 ++ xs2).
Proof.
  induction xs1 as [|x' xs1' IH].
  all: intros xs2 H1.
  -
    contradict H1.
    apply InS_nil_E.
  -
    apply InS_cons_E in H1 as [H1|H1].
    +
      apply InS_cons_I_hd.
      exact H1.
    +
      simpl.
      apply InS_cons_I_tl.
      apply IH.
      exact H1.
Qed.

Lemma InS_app_I_2 `{Setoid X} :
  forall x xs1 xs2,
    InS x xs2 ->
    InS x (xs1 ++ xs2).
Proof.
  induction xs1 as [|x' xs1' IH].
  all: intros xs2 H1.
  -
    exact H1.
  -
    simpl.
    apply IH in H1.
    apply InS_cons_I_tl.
    exact H1.
Qed.

Lemma InS_app_E `{Setoid X} :
  forall x xs1 xs2,
    InS x (xs1 ++ xs2) ->
    InS x xs1 \/
    InS x xs2.
Proof.
  induction xs1 as [|x' xs1' IH].
  all: intros xs2 H1.
  -
    right.
    exact H1.
  -
    simpl in H1.
    apply InS_cons_E in H1 as [H1|H1].
    +
      left.
      left.
      exact H1.
    +
      apply IH in H1 as [H1|H1].
      *
        left.
        right.
        exact H1.
      *
        right.
        exact H1.
Qed.

(** ** Mapping **)

Lemma InS_map_I `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y) (xs : list X) (x : X),
    InS x xs ->
    InS (f x) (map f xs).
Proof.
  induction xs as [|x1 xs' IH].
  all: intros x H1.
  -
    contradict H1.
    apply InS_nil_E.
  -
    apply InS_cons_E in H1 as [H1|H1].
    +
      apply InS_cons_I_hd.
      rewrite H1.
      reflexivity.
    +
      simpl.
      apply InS_cons_I_tl.
      apply IH.
      exact H1.
Qed.

Lemma InS_map_E `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y) (xs : list X) (y : Y),
    InS y (map f xs) ->
    exists x,
      f x == y /\
      InS x xs.
Proof.
  intros f.
  induction xs as [|x xs' IH].
  all: intros y H1.
  -
    contradict H1; apply InS_nil_E.
  -
    simpl in H1.
    apply InS_cons_E in H1 as [H1|H1].
    +
      exists x.
      split.
      *
        symmetry.
        exact H1.
      *
        apply InS_cons_I_hd.
        reflexivity.
    +
      specialize (IH _ H1).
      destruct IH as [x' [H2 H3]].
      exists x'.
      split.
      --
         exact H2.
      --
         apply InS_cons_I_tl.
         exact H3.
Qed.

(** ** Reflection via [inbS] *)

Definition inbS `{EqDec X} (x : X) : list X -> bool :=
  existsb (equiv_decb x).

Lemma InS_reflect_inbS `{EqDec X} :
  forall x xs,
  reflect (InS x xs) (inbS x xs).
Proof.
  induction xs as [|x' xs' IH].
  -
    right.
    apply InS_nil_E.
  -
    simpl.
    destruct IH as [IH|IH].
    +
      rewrite orb_true_r.
      left.
      apply InS_cons_I_tl.
      exact IH.
    +
      rewrite orb_false_r.
      unfold "_ ==b _".
      destruct (x == x') as [H1|H1].
      *
        left.
        apply InS_cons_I_hd.
        exact H1.
      *
        right.
        intros H2.
        apply InS_cons_E in H2 as [H2|H2]; contradiction.
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

(** ** Decidability *)

Corollary InS_dec `{EqDec X} :
  forall x xs,
    {InS x xs} + {~ InS x xs}.
Proof.
  intros x xs.
  eapply reflect_dec.
  apply InS_reflect_inbS.
Qed.

(** ** Miscellaneous *)

Lemma In_InS `{Setoid X} :
  forall (xs : list X) x,
    In x xs ->
    InS x xs.
Proof.
  induction xs as [|x1 xs' IH].
  all: intros x2 H1.
  -
    contradiction.
  -
    destruct H1 as [H1|H1].
    +
      subst x2.
      apply InS_cons_I_hd.
      reflexivity.
    +
      apply InS_cons_I_tl.
      apply IH.
      exact H1.
Qed.

(** * [InS_sublist] *)

Definition InS_sublist `{Setoid X} : relation (list X) :=
  fun xs1 xs2 =>
  forall x,
    InS x xs1 ->
    InS x xs2.

Instance InS_sublist_PreOrder `{Setoid X} :
  PreOrder InS_sublist.
Proof.
  firstorder.
Qed.

(** ** [nil] *)

Fact nil_InS_sublist_I `{Setoid X} :
  forall xs,
    InS_sublist nil xs.
Proof.
  intros xs x H1.
  contradict H1.
  apply InS_nil_E.
Qed.

Fact InS_sublist_nil_E `{Setoid X} :
  forall (xs : list X),
    InS_sublist xs nil ->
    xs = nil.
Proof.
  intros [|x xs'] H1.
  all: try reflexivity.
  exfalso.
  eapply InS_nil_E.
  apply H1.
  left.
  reflexivity.
Qed.

(** ** [cons] *)

Fact cons_InS_sublist_I `{Setoid X} :
  forall x xs1 xs2,
    InS x xs2 ->
    InS_sublist xs1 xs2 ->
    InS_sublist (x :: xs1) xs2.
Proof.
  intros * H1 H2 x H3.
  apply InS_cons_E in H3 as [H3|H3].
  -
    rewrite H3.
    exact H1.
  -
    apply H2.
    exact H3.
Qed.

Fact cons_InS_sublist_E_hd `{Setoid X} :
  forall x xs1 xs2,
    InS_sublist (x :: xs1) xs2 ->
    InS x xs2.
Proof.
  intros * H1.
  apply H1.
  apply InS_cons_I_hd.
  reflexivity.
Qed.

Fact cons_InS_sublist_E_tl `{Setoid X} :
  forall x xs1 xs2,
    InS_sublist (x :: xs1) xs2 ->
    InS_sublist xs1 xs2.
Proof.
  intros * H1 x H2.
  apply H1.
  apply InS_cons_I_tl.
  exact H2.
Qed.

Fact InS_sublist_cons_I `{Setoid X} :
  forall x xs1 xs2,
    InS_sublist xs1 xs2 ->
    InS_sublist xs1 (x :: xs2).
Proof.
  intros * H1 x H2.
  right.
  apply H1.
  exact H2.
Qed.

Instance cons_Proper_InS_sublist `{Setoid X} :
  Proper (equiv ==> InS_sublist ==> InS_sublist) cons.
Proof.
  intros x1 x2 H1 xs1 xs2 H2.
  apply cons_InS_sublist_I.
  -
    apply InS_cons_I_hd.
    exact H1.
  -
    apply InS_sublist_cons_I.
    exact H2.
Qed.

(** ** [map] *)

Instance map_Proper_In_sublist `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y),
    Proper (InS_sublist ==> InS_sublist) (map f).
Proof.
  intros f xs1 xs2 H1 y H2.
  apply InS_map_E in H2 as [x [H2 H3]].
  rewrite <- H2.
  apply InS_map_I.
  apply H1.
  exact H3.
Qed.

(** ** Decidablity *)

Proposition InS_sublist_dec {X} `{EqDec X} :
  forall (xs1 xs2 : list X),
    {InS_sublist xs1 xs2} +
    {exists x, InS x xs1 /\ ~ InS x xs2}.
Proof.
  intros xs1 xs2.
  induction xs1 as [|x xs1' [IH|IH]].
  -
    left.
    apply nil_InS_sublist_I.
  -
    destruct (InS_dec x xs2) as [H2|H2].
    +
      left.
      apply cons_InS_sublist_I; assumption.
    +
      right.
      exists x.
      split.
      *
        apply InS_cons_I_hd.
        reflexivity.
      *
        exact H2.
  -
    right.
    destruct IH as [x' [H2 H3]].
    exists x'.
    split.
    +
      apply InS_cons_I_tl.
      exact H2.
    +
      exact H3.
Qed.

(** * [InS_eq] *)

Definition InS_eq `{Setoid X} : relation (list X) :=
  fun ls rs =>
  InS_sublist ls rs /\
  InS_sublist rs ls.

Instance InS_eq_equiv `{Setoid X} : Equivalence InS_eq.
Proof.
  firstorder.
Qed.

Program Instance InS_eq_Setoid `{Setoid X} : Setoid (list X).

(** ** [nil] *)

Fact InS_eq_nil `{Setoid X} :
  forall (xs : list X),
    InS_eq xs nil ->
    xs = nil.
Proof.
  intros xs [H1 H2].
  apply InS_sublist_nil_E.
  exact H1.
Qed.

(** ** [cons] *)

Instance cons_Proper_InS_eq `{Setoid X} :
  Proper (equiv ==> InS_eq ==> InS_eq) cons.
Proof.
  intros x1 x2 H1 xs1 xs2 [H2 H3].
  split.
  all: rewrite H1.
  all: rewrite H2 + rewrite H3.
  all: reflexivity.
Qed.

Lemma In_eq_cons_cons `{Setoid X} :
  forall (x1 x2 : X) xs,
    InS_eq (x1 :: x2 :: xs) (x2 :: x1 :: xs).
Proof.
  intros *.
  split.
  all: intros x H1.
  all: apply InS_cons_E in H1 as [H1|H1].
  all: try apply InS_cons_E in H1 as [H1|H1].
  all: (left + (right; left + right); exact H1).
Qed.

(** ** [app] *)

Instance app_Proper `{Setoid X} :
  Proper (InS_eq ==> InS_eq ==> InS_eq) (@app X).
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  split.
  all: intros x H3.
  all: apply InS_app_E in H3 as [H3|H3].
  all: apply H1 in H3 + apply H2 in H3.
  all: apply InS_app_I_1 + apply InS_app_I_2; exact H3.
Qed.

Lemma In_eq_app_comm `{Setoid X} :
  forall (xs1 xs2 : list X),
    InS_eq (xs1 ++ xs2) (xs2 ++ xs1).
Proof.
  intros xs1 xs2.
  split.
  all: intros x H1.
  all: apply InS_app_E in H1 as [H1|H1].
  all: apply InS_app_I_1 + apply InS_app_I_2; exact H1.
Qed.

(** ** [map] *)

Instance map_Proper_In_eq `{Setoid X} `{Setoid Y} :
  forall (f : Morph X Y),
    Proper (InS_eq ==> InS_eq) (map f).
Proof.
  intros f xs1 xs2 [H1 H2].
  split.
  all: rewrite H1 + rewrite H2.
  all: reflexivity.
Qed.

(** ** Decidability *)

Instance InS_eq_dec `{EqDec X} : EqDec InS_eq_Setoid.
Proof.
  intros xs1 xs2.
  destruct (InS_sublist_dec xs1 xs2) as [H1|H1].
  -
    destruct (InS_sublist_dec xs2 xs1) as [H2|H2].
    +
      left.
      split; assumption.
    +
      right.
      destruct H2 as [x [H2 H3]].
      intros [H4 H5].
      apply H3.
      apply H5.
      exact H2.
  -
    right.
    destruct H1 as [x [H1 H2]].
    intros [H3 H4].
    apply H2.
    apply H3.
    exact H1.
Qed.

(** ** Miscellaneous *)

Lemma InS_sublist_singleton_E `{EqDec X} :
  forall (xs : list X) (x : X),
    InS_sublist xs (x :: nil) ->
    InS_eq xs (x :: nil) \/
    InS_eq xs nil.
Proof.
  intros xs x1 H1.
  destruct (InS_dec x1 xs) as [H2|H2].
  -
    left.
    split; try exact H1.
    apply cons_InS_sublist_I.
    +
      exact H2.
    +
      apply nil_InS_sublist_I.
  -
    right.
    destruct xs as [|x2 xs']; try reflexivity.
    exfalso.
    apply H2.
    apply cons_InS_sublist_E_hd in H1 as H3.
    apply cons_InS_sublist_E_tl in H1 as H4.
    apply InS_cons_E in H3 as [H3|H3].
    +
      apply InS_cons_I_hd.
      symmetry.
      exact H3.
    +
      contradict H3.
      apply InS_nil_E.
Qed.

(** * Well-Founded Relations on Lists *)
(** ** [length_order] *)

Definition length_order {X} : relation (@list X) :=
  fun xs1 xs2 =>
  length xs1 < length xs2.

Lemma length_order_Acc {X} :
  forall s (xs : list X),
    length xs <= s ->
    Acc length_order xs.
Proof.
  induction s as [|s' IH].
  all: intros xs1 H1.
  all: constructor.
  all: intros xs2 H2.
  all: red in H2.
  all: try apply IH.
  all: lia.
Qed.

Proposition length_order_wf {X} :
  well_founded (@length_order X).
Proof.
  intro.
  eapply length_order_Acc.
  reflexivity.
Qed.

Definition length_order_ind {X} := well_founded_ind (@length_order_wf X).

(** ** [InS_sublist_order] *)

Definition InS_sublist_order `{Setoid X} : relation (@list X) :=
  fun xs1 xs2 =>
  InS_sublist xs1 xs2 /\
  exists x,
    InS x xs2 /\
    ~ InS x xs1.

Lemma InS_sublist_order_Acc `{EqDec X} :
  forall xs1 xs2,
    InS_sublist xs2 xs1 ->
    Acc InS_sublist_order xs2.
Proof.
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
    (* TODO extract? *)
    induction xs1 as [|x2 xs1' IH].
    +
      easy.
    +
      unfold length_order in *.
      unfold "_ <>b _" in *.
      unfold "_ ==b _" in *.
      simpl in *.
      apply InS_cons_E in H2 as [H2|H2].
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
           (* TODO extract? *)
           assert (H4 :
            filter
            (fun y : X => negb (if x1 == y then true else false))
            xs1' =
            xs1'
          ).
          {
            clear dependent x2.
            rename xs1' into xs1.
            (* TODO extract? *)
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
Qed.

Proposition InS_sublist_order_wf `{EqDec X} :
  well_founded InS_sublist_order.
Proof.
  intro.
  eapply InS_sublist_order_Acc.
  reflexivity.
Qed.

Definition InS_sublist_order_ind `{EqDec X} :=
  well_founded InS_sublist_order.

(** * [mult] *)

Definition mult `{Setoid X} (P : Morph X Prop) (xs : list X) : Prop :=
  forall x,
    InS x xs ->
    P x.

Instance mult_Proper_InS_eq `{Setoid X} :
  Proper (Morph_eq ==> InS_eq ==> iff) mult.
Proof.
  intros f1 f2 H1 xs1 xs2 H2.
  split.
  all: intros H3 x H4.
  all: apply H1.
  all: apply H3.
  all: apply H2.
  all: exact H4.
Qed.

(** ** [nil] *)

Fact mult_nil_I `{Setoid X} :
  forall P,
    mult P nil.
Proof.
  intros P x H1.
  contradict H1.
  apply InS_nil_E.
Qed.

(** ** [cons] *)

Fact mult_cons_I `{Setoid X} :
  forall (P : Morph X Prop) x xs,
    P x ->
    mult P xs ->
    mult P (x :: xs).
Proof.
  intros P x1 xs H1 H2 x2 H3.
  apply InS_cons_E in H3 as [H3|H3].
  -
    rewrite H3.
    exact H1.
  -
    apply H2.
    exact H3.
Qed.

Fact mult_cons_E_hd `{Setoid X} :
  forall P x xs,
    mult P (x :: xs) ->
    P x.
Proof.
  intros P x xs H1.
  apply H1.
  apply InS_cons_I_hd.
  reflexivity.
Qed.

Fact mult_cons_E_tl `{Setoid X} :
  forall P x xs,
    mult P (x :: xs) ->
    mult P xs.
Proof.
  intros P x1 xs H1 x2 H2.
  apply H1.
  apply InS_cons_I_tl.
  exact H2.
Qed.

(** ** [app] *)

Lemma mult_app_I `{Setoid X} :
  forall P xs1 xs2,
    mult P xs1 ->
    mult P xs2 ->
    mult P (xs1 ++ xs2).
Proof.
  intros * H1 H2 x H3.
  apply InS_app_E in H3 as [H3|H3].
  all: apply H1 + apply H2; exact H3.
Qed.

Lemma mult_app_E_1 `{Setoid X} :
  forall P xs1 xs2,
    mult P (xs1 ++ xs2) ->
    mult P xs1.
Proof.
  intros * H1 x H2.
  apply H1.
  apply InS_app_I_1.
  exact H2.
Qed.

Lemma mult_app_E_2 `{Setoid X} :
  forall P xs1 xs2,
    mult P (xs1 ++ xs2) ->
    mult P xs2.
Proof.
  intros * H1 x H2.
  apply H1.
  apply InS_app_I_2.
  exact H2.
Qed.

(** * [some] *)

Definition some `{Setoid X} (P : Morph X Prop) (xs : list X) : Prop :=
  exists x,
    InS x xs /\
    P x.

Instance some_Proper_InS_eq `{Setoid X} :
  Proper (Morph_eq ==> InS_eq ==> iff) some.
Proof.
  intros P1 P2 H1 xs1 xs2 H2.
  split.
  all: intros [x [H3 H4]].
  all: exists x.
  all: apply H1 in H4.
  all: apply H2 in H3.
  all: split.
  all: assumption.
Qed.

(** ** [nil] *)

Fact some_nil_E `{Setoid X} :
  forall P,
    ~ some P nil.
Proof.
  intros P [x [H1 H2]].
  contradict H1.
  apply InS_nil_E.
Qed.

(** ** [cons] *)

Fact some_cons_I_hd `{Setoid X} :
  forall (P : Morph X Prop) x xs,
    P x ->
    some P (x :: xs).
Proof.
  intros * H1.
  eexists.
  split; try exact H1.
  apply InS_cons_I_hd.
  reflexivity.
Qed.

Fact some_cons_I_tl `{Setoid X} :
  forall P x xs,
    some P xs ->
    some P (x :: xs).
Proof.
  intros * [x [H1 H2]].
  eexists.
  split; try exact H2.
  apply InS_cons_I_tl.
  exact H1.
Qed.

Fact some_cons_E `{Setoid X} :
  forall P x xs,
    some P (x :: xs) ->
    P x \/
    some P xs.
Proof.
  intros * [x [H1 H2]].
  apply InS_cons_E in H1 as [H1|H1].
  -
    left.
    rewrite H1 in H2.
    exact H2.
  -
    right.
    eexists.
    split; eassumption.
Qed.

(** ** [app] *)

Lemma some_app_I_1 `{Setoid X} :
  forall P xs1 xs2,
    some P xs1 ->
    some P (xs1 ++ xs2).
Proof.
  intros * [x [H1 H2]].
  exists x.
  split; try exact H2.
  apply InS_app_I_1.
  exact H1.
Qed.

Lemma some_app_I_2 `{Setoid X} :
  forall P xs1 xs2,
    some P xs2 ->
    some P (xs1 ++ xs2).
Proof.
  intros * [x [H1 H2]].
  exists x.
  split; try exact H2.
  apply InS_app_I_2.
  exact H1.
Qed.

Lemma some_app_E `{Setoid X} :
  forall P xs1 xs2,
    some P (xs1 ++ xs2) ->
    some P xs1 \/
    some P xs2.
Proof.
  intros * [x [H1 H2]].
  apply InS_app_E in H1 as [H1|H1].
  -
    left.
    eexists.
    split; eassumption.
  -
    right.
    eexists.
    split; eassumption.
Qed.

(** * Finiteness and Decidablity

   The contents of this section where discussed in a Stack Exchange Post:
   https://proofassistants.stackexchange.com/questions/4690/prove-decidability-on-finite-types
 *)


Lemma list_choose {X} (P Q : X -> Prop) :
  forall xs,
    (forall x, In x xs -> {P x} + {Q x}) ->
    {x | In x xs /\ P x} + {forall x, In x xs -> Q x}.
Proof.
  induction xs as [|x xs' IH].
  all: intros H1.
  -
    right.
    intros x H2.
    contradiction.
  -
    destruct (H1 x (or_introl eq_refl)) as [H2|H2].
    +
      left.
      exists x.
      firstorder.
    +
      destruct IH as [IH|IH].
      {
        firstorder.
      }
      *
        destruct IH as [x' [H3 H4]].
        left.
        exists x'.
        firstorder.
      *
        right.
        firstorder.
        congruence.
Qed.

Proposition finite_choice {X} (P : X -> Prop) :
  forall (xs : list X),
    (forall x, In x xs) ->
    (forall x, {P x} + {~ P x}) ->
    {forall x, P x} + {~ forall x, P x}.
Proof.
  intros xs H1 H2.
  destruct (list_choose (fun x => ~ P x) P xs) as [H3|H3].
  {
    firstorder.
  }
  -
    right.
    firstorder.
  -
    left.
    firstorder.
Qed.
