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
