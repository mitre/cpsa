(** * Monadic Operations on Option Types *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** Haskell do-like notation for option types *)

Notation "x <- M ;; N" := (match M with None => None | Some x => N end)
  (at level 30, right associativity).

Lemma do_some:
  forall A B (f: option A) (g: A -> option B) b,
    x <- f;; g x = Some b ->
    exists a, f = Some a /\ g a = Some b.
Proof.
  intros.
  destruct f as [x|].
  - exists x; auto.
  - inversion H.
Qed.

(** Monadic map *)

Fixpoint map_m {A B} (f: A -> option B) (l: list A): option (list B) :=
  match l with
  | [] => Some []
  | x :: xs =>
    y <- f x;;
    ys <- map_m f xs;;
    Some (y :: ys)
  end.

Lemma map_m_nil:
  forall A B (f: A -> option B) x xs,
    map_m f (x :: xs) <> Some [].
Proof.
  intros.
  intro.
  simpl in H.
  apply do_some in H.
  destruct H as [y H].
  destruct H as [H G].
  apply do_some in G.
  destruct G as [ys G].
  destruct G as [G F].
  inversion F.
Qed.

Lemma map_m_pair:
  forall A B (f: A -> option B) x xs y ys,
    map_m f (x :: xs) = Some (y :: ys) ->
    f x = Some y /\ map_m f xs = Some ys.
Proof.
  intros.
  simpl in H.
  apply do_some in H.
  destruct H as [z H].
  destruct H as [H G].
  apply do_some in G.
  destruct G as [zs G].
  destruct G as [G F].
  inversion F; subst; auto.
Qed.

(** Monadic fold *)

Fixpoint fold_m {A B} (f: A -> B -> option A)
         (a: A) (l: list B): option A :=
  match l with
  | [] => Some a
  | x :: xs =>
    b <- f a x;;
    fold_m f b xs
  end.
