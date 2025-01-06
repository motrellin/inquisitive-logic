From Coq Require Import Bool List.

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

End inb.
