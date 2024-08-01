From Coq Require Export List.
From InqLog.Prop Require Export LP.

Fixpoint list_func {X Y} (xs : list X) (ys : list Y) : list (list (X*Y)) :=
  match xs with
  | nil => nil
  | x :: nil => map (fun y => (x,y) :: nil) ys
  | x :: xs' =>
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
      (list_func xs' ys)
  end.

Compute (list_func (1 :: 2 :: nil) (3 :: 4 :: nil)).
Compute length (list_func (1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: nil)).


Definition resolution : form -> list form :=
  form_rect
  _
  (fun a => (atom a) :: nil)
  (bot :: nil)
  (fun f1 r1 f2 r2 => flat_map (fun x => map (fun y => conj x y) r2) r1)
  (fun f1 r1 f2 r2 =>
    map
    (
      fun f =>
      list_rect
      _
      top
      (fun x _ rest => conj (impl (fst x) (snd x)) rest)
      f
    )
    (list_func r1 r2)
  )
  (fun f1 r1 f2 r2 => r1 ++ r2).

Compute (resolution (iquest (atom 0))).
Compute (resolution (impl (iquest (atom 0)) (iquest (atom 1)))).
