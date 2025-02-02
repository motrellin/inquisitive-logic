From Coq Require Export Setoid SetoidDec.

Generalizable Variables X Y.

Record Morph (X Y : Type) `{Setoid X} `{Setoid Y} :=
  {
    morph : X -> Y;
    morph_Proper :: Proper (equiv ==> equiv) morph
  }.

Coercion morph : Morph >-> Funclass.

Definition Morph_eq
  `{Setoid X}
  `{Setoid Y}
  `(f : Morph X Y)
  `(g : Morph X Y) : Prop :=
  forall x,
    f x == g x.

Instance Morph_eq_Equiv
  `{Setoid X}
  `{Setoid Y}
  : Equivalence (@Morph_eq X _ Y _).
Proof.
  constructor.
  -
    intros f x.
    reflexivity.
  -
    intros f g H1 x.
    red in H1.
    rewrite H1.
    reflexivity.
  -
    intros f g h H1 H2 x.
    red in H1, H2.
    rewrite H1, H2.
    reflexivity.
Qed.

Instance Morph_Setoid
  `{Setoid X}
  `{Setoid Y}
  : Setoid (Morph X Y) :=
  {|
    equiv := Morph_eq;
    setoid_equiv := Morph_eq_Equiv
  |}.
