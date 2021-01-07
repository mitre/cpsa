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
    forallb (fun x => is_chan x || is_basic x) (inputs r) &&
    forallb (well_typed decls) (outputs r) &&
    forallb (flip not_in (uniqs r)) (inputs r) &&
    forallb (flip not_in (outputs r)) (inputs r)
  end.

(** Executions are roles with exceptions.

    - No variables of sort message are allowed in its trace.

    - The order in which uniques occur in an execution is significant,
      but it is not for a role.  In an execution, the order of the
      uniques determines the order in which they are used to generate
      nonces.  Within a role, uniques are just a set of basic
      values. *)

Definition is_not_mesg_decl (d: decl): bool :=
  negb (type_eqb (snd d) Mesg).

(** Is [r] a valid execution?  *)

Definition valid_exec (r: role): bool :=
  match fold_m well_formed_event nil (trace r) with
  | None => false
  | Some decls =>
    forallb is_not_mesg_decl decls &&
    forallb (well_typed decls) (uniqs r) &&
    forallb (flip orig (trace r)) (uniqs r) &&
    forallb is_basic (uniqs r) &&
    has_no_dups (uniqs r) &&
    forallb (well_typed_with_chan decls) (inputs r) &&
    forallb (fun x => is_chan x || is_basic x) (inputs r) &&
    forallb (well_typed decls) (outputs r) &&
    forallb (flip not_in (uniqs r)) (inputs r) &&
    forallb (flip not_in (outputs r)) (inputs r)
  end.
