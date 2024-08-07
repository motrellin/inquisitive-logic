From Coq Require Export List.

Section list_func_helper.

  Context {X : Type}.
  Context {Y : Type}.
  Context (x : X).
  Context (xs' : list X).
  Context (R : list Y -> list (list (X*Y))).

  Definition list_func_helper : list Y -> list (list (X*Y)) :=
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
      (R ys)
    )
    xs'.

End list_func_helper.

Definition list_func {X Y} : list X -> list Y -> list (list (X*Y)) :=
  list_rect
  _
  (fun ys => nil) (* Base Case *)
  list_func_helper (* Recursive Case *).

Compute (list_func (1 :: 2 :: nil) (3 :: 4 :: nil)).
Compute length (list_func (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)).
