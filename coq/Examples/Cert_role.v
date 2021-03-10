(** Protocol: cert (cert.scm:1:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (cert.scm:2:3) *)

Definition init_role: role :=
  mkRole
  [Sd 0 (En (Tx 2) (Ik (Av 1)))]
  []
  [Ch 0; Ak (Av 1); En (Tx 2) (Ik (Av 1))]
  [].
