Require Import List ListSet Bool Program Monad Alg.

(** * Protocol Roles *)

Record role: Set :=
  mkRole {
      trace: list evt;
      uniqs: list alg;
      inputs: list alg;
      outputs: list alg }.

(** Is [x] not in list [l]? *)

Definition not_in (x: alg) (l: list alg): bool :=
  negb (set_mem alg_dec x l).

(** Does list [l] contain duplicates? *)

Fixpoint has_no_dups (l: list alg): bool :=
  match l with
  | nil => true
  | x :: xs => not_in x xs && has_no_dups xs
  end.

(** Is [p] a valid role? *)

Definition valid_role (p: role): bool :=
  match fold_m well_formed_event nil (trace p) with
  | None => false
  | Some decls =>
    forallb (well_sorted decls) (uniqs p) &&
    forallb (flip orig (trace p)) (uniqs p) &&
    forallb is_basic (uniqs p) &&
    has_no_dups (uniqs p) &&
    forallb (well_sorted_with_chan decls) (inputs p) &&
    forallb (fun x => is_chan x || is_basic x) (inputs p) &&
    forallb (well_sorted decls) (outputs p) &&
    forallb (flip not_in (uniqs p)) (inputs p) &&
    forallb (flip not_in (outputs p)) (inputs p)
  end.
