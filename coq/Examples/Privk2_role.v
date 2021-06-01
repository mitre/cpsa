(** Protocol: privk2 (privk2.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (privk2.scm:4:3) *)

Definition rho_role: role :=
  mkRole
  [Rv 1 (En (Pr (Nm 0) (Ik (Pb2 "enc" 0))) (Ak (Av 2)));
   Sd 1 (En (Nm 0) (Ik (Pb2 "enc" 0)))]
  []
  [Ch 1; Ik (Av 2)]
  [].
