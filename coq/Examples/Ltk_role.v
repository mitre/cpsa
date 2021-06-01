(** Protocol: ltk (ltk.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (ltk.scm:4:3) *)

Definition rho_role: role :=
  mkRole
  [Rv 2 (En (Pr (Nm 0) (Pr (Nm 1) (Sk (Lt 0 1)))) (Ak (Av 3)));
   Sd 2 (En (Pr (Nm 0) (Nm 1)) (Sk (Lt 0 1)))]
  []
  [Ch 2; Ik (Av 3)]
  [].
