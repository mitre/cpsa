Require Import List ListSet Bool Program Monad Proc Alg.

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

(** Is [r] a valid role? *)

Definition valid_role (r: role): bool :=
  match fold_m well_formed_event nil (trace r) with
  | None => false
  | Some decls =>
    forallb (well_typed decls) (uniqs r) &&
    forallb (flip orig (trace r)) (uniqs r) &&
    forallb is_basic (uniqs r) &&
    has_no_dups (uniqs r) &&
    forallb (well_typed_with_chan decls) (inputs r) &&
    forallb (fun t => is_basic t || is_chan t) (inputs r) &&
    forallb receivable (map evt_msg (trace r)) &&
    forallb receivable (outputs r) &&
    forallb (well_typed decls) (outputs r) &&
    forallb (flip not_in (uniqs r)) (inputs r) &&
    forallb (flip not_in (outputs r)) (inputs r)
  end.
