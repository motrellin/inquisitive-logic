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

(** * Subset Types *)

Definition sig_eq `{Setoid X} (P : Morph X Prop) : relation {x : X | P x} :=
  fun x1 x2 =>
  (proj1_sig x1 == proj1_sig x2)%type.

Instance sig_eq_Equiv `{Setoid X} (P : Morph X Prop) :
  Equivalence (sig_eq P).
Proof.
  unfold sig_eq.
  constructor.
  -
    intros [].
    reflexivity.
  -
    intros [] [] H1.
    symmetry.
    exact H1.
  -
    intros [] [] [] H1 H2.
    etransitivity; eassumption.
Qed.

Instance sig_Setoid `{Setoid X} (P : Morph X Prop) : Setoid (sig P) :=
  {|
    equiv := sig_eq P;
    setoid_equiv := sig_eq_Equiv P
  |}.

Instance sig_EqDec `{EqDec X} (P : Morph X Prop) :
  EqDec (sig_Setoid P).
Proof.
  intros [x H1] [y H2].
  destruct (x == y) as [H3|H3].
  -
    left.
    exact H3.
  -
    right.
    intros H4.
    apply H3.
    exact H4.
Qed.

Instance proj1_sig_Proper `{S : Setoid X} (P : Morph X Prop) :
  Proper (sig_eq P ==> @equiv X S) (@proj1_sig X P).
Proof.
  intros x y H3.
  exact H3.
Qed.

Lemma sig_eq_lifting `{S : Setoid X} (P : Morph X Prop) :
  forall x y (C1 : P x) (C2 : P y),
    x == y ->
    sig_eq P (exist P x C1) (exist P y C2).
Proof.
  intros x y C1 C2 H1.
  exact H1.
Qed.

(** * Regarding Autosubst *)

Instance scons_Proper `{Setoid X} :
  Proper (equiv ==> ext_eq ==> ext_eq) (@scons X).
Proof.
  intros x1 x2 H1 f1 f2 H2 [|x'].
  all: simpl.
  -
    exact H1.
  -
    apply H2.
Qed.
