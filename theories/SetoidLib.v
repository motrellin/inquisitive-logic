From InqLog Require Export Prelude.

Generalizable Variables X Y.

(** * Morphisms

   We want to have morphisms between arbitrary setoids.
   Such morphisms are functions which respect the carried
   equivalence relations by the setoids.
 *)

Record Morph (X Y : Type) `{Setoid X} `{Setoid Y} :=
  {
    morph : X -> Y;
    morph_Proper :: Proper (equiv ==> equiv) morph
  }.

(**
   We define the projection [morph] to be a [Coercion]. By
   this, it get's easier to use morphisms as standard
   functions.
 *)
Coercion morph : Morph >-> Funclass.

(** * Extensional Equality

   We often need function to be extensional equal. This
   meaning is captured by the following definition.
 *)

Definition ext_eq {X} `{Setoid Y} : relation (X -> Y) :=
  fun f g =>
  forall x,
    f x == g x.

Instance ext_eq_Equiv {X} `{Setoid Y} :
  Equivalence (@ext_eq X Y _).
Proof.
  constructor.
  -
    intros f x.
    reflexivity.
  -
    intros f g H1 x.
    now symmetry.
  -
    intros f g h H1 H2 x.
    now etransitivity.
Qed.

Program Instance ext_eq_Setoid {X} `{Setoid Y} :
  Setoid (X -> Y).

Definition Morph_eq `{Setoid X} `{Setoid Y} :
  relation (Morph X Y) :=

  ext_eq.

Instance Morph_eq_Equiv `{Setoid X} `{Setoid Y} :
  Equivalence (@Morph_eq X _ Y _).
Proof.
  constructor.
  -
    intros f x.
    reflexivity.
  -
    intros f g H1 x.
    now symmetry.
  -
    intros f g h H1 H2 x.
    now etransitivity.
Qed.

Program Instance Morph_Setoid `{Setoid X} `{Setoid Y} :
  Setoid (Morph X Y).

Program Canonical to_Morph {X} `{Setoid Y} (f : X -> Y) :
  @Morph X Y (eq_setoid _) _ :=

  {|
    morph := f
  |}.
