(** Protocol: nsl (nsl.scm:3:1) *)

Require Import String List Alg Sem.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (nsl.scm:4:3) *)

Definition init_role: role :=
  mkRole
  [Sd 2 (En (Pr (Tx 3) (Ak (Av 0))) (Ak (Av 1)));
   Rv 2 (En (Pr (Tx 3) (Pr (Tx 4) (Ak (Av 1)))) (Ak (Av 0)));
   Sd 2 (En (Tx 4) (Ak (Av 1)))]
  [Tx 3]
  [Ch 2; Ik (Av 0); Ak (Av 0); Ak (Av 1)]
  [Tx 3; Tx 4].

(** Role: resp (nsl.scm:13:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 2 (En (Pr (Tx 3) (Ak (Av 0))) (Ak (Av 1)));
   Sd 2 (En (Pr (Tx 3) (Pr (Tx 4) (Ak (Av 1)))) (Ak (Av 0)));
   Rv 2 (En (Tx 4) (Ak (Av 1)))]
  [Tx 4]
  [Ch 2; Ik (Av 1); Ak (Av 1); Ak (Av 0)]
  [Tx 4; Tx 3].
