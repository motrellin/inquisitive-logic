From Coq Require Export List.

Definition list_func {X Y} : list X -> list Y -> list (list (X*Y)) :=
  list_rect
  _
  (fun ys => nil :: nil)
  (fun x xs' R =>
    list_rect
    _
    nil
    (fun y ys' _ =>
      flat_map (fun xys => map (fun y => (x,y) :: xys) (y :: ys')) (R (y :: ys'))
    )
  ).

Compute (list_func (1 :: 2 :: nil) (3 :: 4 :: nil)).
Compute length (list_func (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)).
