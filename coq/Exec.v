(** * Executable Roles

    Every executable role will be compiled. *)

Require Import Proc Alg Role Derives Comp.

(** A member [y] of [ys] is reducible iff every encryption carried by
    y can be decrypted and every hash can be synthesized.  *)

Definition reducible (xs ys: list alg): Prop :=
  forall y,
    In y ys ->
    (forall x k,
        carried_by (En x k) y ->
        derives (ys ++ xs) (inv k)) /\
    (forall x,
        carried_by (Hs x) y ->
        derives (ys ++ xs) x).

(** ** Executable Role

    A role is executable iff

    - the role is valid,

    - the input is reducible, and

    - the trace is executable.

    A trace is executable iff

    - the outputs can be derived from previous messaging,

    - sent terms can be derived from previous messaging, and

    - received terms are reducible given previous messaging. *)

Fixpoint exec_tr (xs: list alg) (tr: list evt)
         (us: list (list alg)) (outs: list alg): Prop :=
  match tr, us with
  | nil, nil =>
    forall x,
      In x outs ->
      derives xs x
  | Sd v x :: tr, u :: us =>
    derives (u ++ xs) (Ch v) /\
    derives (u ++ xs) x /\
    exec_tr (u ++ xs) tr us outs
  | Rv v x :: tr, us =>
    derives xs (Ch v) /\
    reducible xs (x :: nil) /\
    exec_tr (x :: xs) tr us outs
  | _, _ => False
  end.

Definition exec_rl (rl: role): Prop :=
  valid_role rl = true /\
  reducible nil (inputs rl) /\
  exec_tr (rev (inputs rl))
          (trace rl)
          (uniq_list (trace rl) (uniqs rl))
          (outputs rl).

(** When the compiler is presented with an executable role, it will
    produce code. *)

Conjecture exec_implies_comp:
  forall (rl: role),
    exec_rl rl ->
    exists (cs: store) (p: proc),
      comp rl cs p.
