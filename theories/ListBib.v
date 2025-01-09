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

  Corollary In_iff_inb :
    forall x xs,
      In x xs <->
      inb x xs = true.
  Proof.
    intros x xs.
    apply reflect_iff.
    apply In_reflect_inb.
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
