(** * Monadic Operations on Option Types *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** Haskell do-like notation for option types *)

Notation "x <- M ; N" := (match M with None => None | Some x => N end)
  (at level 30, right associativity).

(** Monadic map *)

Fixpoint map_m {A B} (f: A -> option B) (l: list A): option (list B) :=
  match l with
  | [] => Some []
  | x :: xs =>
    y <- f x;
    ys <- map_m f xs;
    Some (y :: ys)
  end.

(** Monadic fold *)

Fixpoint fold_m {A B} (f: A -> B -> option A)
         (a: A) (l: list B): option A :=
  match l with
  | [] => Some a
  | x :: xs =>
    b <- f a x;
    fold_m f b xs
  end.
