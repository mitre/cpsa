(** Protocol: privk (privk.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (privk.scm:4:3) *)

Definition rho_role: role :=
  mkRole
  [Rv 1 (En (Pr (Nm 0) (Ik (Pb 0))) (Ak (Av 2)));
   Sd 1 (En (Nm 0) (Ik (Pb 0)))]
  []
  [Ch 1; Ik (Av 2)]
  [].
