(** Protocol: invk (invk.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (invk.scm:4:3) *)

Definition rho_role: role :=
  mkRole
  [Rv 1 (Pr (Nm 0) (Ik (Av 2))); Sd 1 (En (Nm 0) (Ak (Av 2)))]
  []
  [Ch 1; Ak (Av 2)]
  [].
