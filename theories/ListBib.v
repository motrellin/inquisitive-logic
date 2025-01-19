From Coq Require Export Bool List Morphisms Setoid.

Section inb.

  Context {X : Type}.
  Context (X_deceq :
    forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}
  ).

  Fixpoint inb (x : X) (xs : list X) : bool :=
    match xs with
    | nil => false
    | x' :: xs' =>
        if X_deceq x' x
        then true
        else inb x xs'
    end.

  Theorem In_reflect_inb :
    forall x xs,
      reflect (In x xs) (inb x xs).
  Proof.
    intros x.
    induction xs as [|x' xs' IH].
    -
      constructor.
      easy.
    -
      simpl.
      destruct (X_deceq x' x) as [H1|H1].
      +
        constructor.
        left.
        exact H1.
      +
        destruct IH as [IH|IH].
        all: constructor.
        *
          right.
          exact IH.
        *
          firstorder.
  Qed.

  Corollary In_iff_inb_true :
    forall x xs,
      In x xs <->
      inb x xs = true.
  Proof.
    intros x xs.
    apply reflect_iff.
    apply In_reflect_inb.
  Qed.

  Corollary In_iff_inb_false :
    forall x xs,
      (~ In x xs) <->
      inb x xs = false.
  Proof.
    intros x xs.
    split.
    -
      intros H1.
      destruct (inb x xs) eqn:H2; try reflexivity.
      apply In_iff_inb_true in H2.
      contradiction.
    -
      intros H1 H2.
      apply In_iff_inb_true in H2.
      congruence.
  Qed.

  Corollary In_iff_inb :
    forall x xs y ys,
      (In x xs <-> In y ys) <->
      inb x xs = inb y ys.
  Proof.
    intros x xs y ys.
    split.
    -
      intros H1.
      destruct (inb y ys) eqn:H2.
      +
        apply In_iff_inb_true.
        apply H1.
        apply In_iff_inb_true.
        exact H2.
      +
        apply In_iff_inb_false.
        intros H3.
        apply H1 in H3.
        apply In_iff_inb_true in H3.
        congruence.
    -
      intros H1.
      split.
      all: intros H2.
      all: apply In_iff_inb_true.
      +
        rewrite <- H1.
        apply In_iff_inb_true.
        exact H2.
      +
        rewrite H1.
        apply In_iff_inb_true.
        exact H2.
  Qed.

End inb.

Definition In_eq {X} : relation (list X) :=
  fun ls rs =>
  forall x,
    In x ls <->
    In x rs.

Instance In_eq_equiv {X} : Equivalence (@In_eq X).
Proof.
  split.
  -
    intros xs1 x.
    reflexivity.
  -
    intros xs1 xs2 H1 x.
    symmetry.
    apply H1.
  -
    intros xs1 xs2 xs3 H1 H2 x.
    etransitivity; eauto.
Qed.

Lemma In_eq_nil {X} :
  forall (xs : list X),
    In_eq xs nil ->
    xs = nil.
Proof.
  destruct xs as [|x xs'].
  -
    reflexivity.
  -
    intros H1.
    specialize (H1 x) as [H1 _].
    exfalso.
    apply H1.
    left.
    reflexivity.
Qed.

Instance cons_Proper {X} :
  Proper (@eq X ==> In_eq ==> In_eq) cons.
Proof.
  intros x1 x2 H1 xs1 xs2 H2 x.
  subst x2.
  split.
  all: intros [H3|H3].
  all: try (left; exact H3).
  all: try (right; apply H2; exact H3).
Qed.

Lemma In_eq_cons_cons {X} :
  forall (x1 x2 : X) xs,
    In_eq (x1 :: x2 :: xs) (x2 :: x1 :: xs).
Proof.
  intros * x.
  split.
  all: intros [H1|[H1|H1]].
  all: (left + (right; left + right); exact H1).
Qed.

Instance app_Proper {X} :
  Proper (In_eq ==> In_eq ==> In_eq) (@app X).
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2 x.
  split.
  all: intros H3.
  all: apply in_app_iff.
  all: apply in_app_iff in H3 as [H3|H3].
  all: apply H1 in H3 + apply H2 in H3.
  all: left + right; exact H3.
Qed.

Lemma In_eq_app_comm {X} :
  forall (xs1 xs2 : list X),
    In_eq (xs1 ++ xs2) (xs2 ++ xs1).
Proof.
  intros xs1 xs2 x.
  split.
  all: intros H1.
  all: apply in_app_iff.
  all: apply in_app_iff in H1 as [H1|H1].
  all: left + right; exact H1.
Qed.

Definition In_sublist {X} : relation (list X) :=
  fun xs2 xs1 =>
  forall x,
    In x xs2 ->
    In x xs1.

Instance In_sublist_PreOrder {X} :
  PreOrder (@In_sublist X).
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

Lemma In_sublist_singleton {X} (X_deceq : forall (x y : X), {x = y} + {x <> y}) :
  forall (xs : list X) (x : X),
    In_sublist xs (x :: nil) ->
    In_eq xs (x :: nil) \/
    xs = nil.
Proof.
  intros xs x1 H1.
  destruct (In_dec X_deceq x1 xs) as [H2|H2].
  -
    left.
    intros x2.
    split.
    +
      auto.
    +
      intros [H3|H3].
      *
        subst x2.
        exact H2.
      *
        contradiction.
  -
    right.
    destruct xs as [|x2 xs'].
    +
      reflexivity.
    +
      exfalso.
      assert (H3 : In x2 (x2 :: xs')). left; reflexivity.
      apply H1 in H3 as H4.
      destruct H4 as [H4|H4].
      *
        congruence.
      *
        contradiction.
Qed.
