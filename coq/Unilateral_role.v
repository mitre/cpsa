(** Protocol: unilateral (../rtst/unilateral.scm:5:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (../rtst/unilateral.scm:6:3) *)

Definition init_role: role :=
  mkRole
  [Sd 0 (En (Tx 2) (Ak (Av 1))); Rv 0 (Tx 2)]
  [Tx 2]
  [Ch 0; Ak (Av 1)]
  [Tx 2].

(** Role: resp (../rtst/unilateral.scm:14:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 0 (En (Tx 2) (Ak (Av 1))); Sd 0 (Tx 2)]
  []
  [Ch 0; Ik (Av 1)]
  [Tx 2].
