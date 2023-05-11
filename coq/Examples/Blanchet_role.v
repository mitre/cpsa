(** Protocol: blanchet-fixed (blanchet.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (blanchet.scm:4:3) *)

Definition init_role: role :=
  mkRole
  [Sd 2 (En (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Rv 2 (En (Dt 3) (Sk (Sv 4)))]
  [Sk (Sv 4)]
  [Ch 2; Nm 1; Ik (Pb 0); Ak (Pb 1)]
  [Dt 3; Sk (Sv 4)].

(** Role: resp (blanchet.scm:12:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 2 (En (En (Pr (Sk (Sv 4)) (Nm 1)) (Ik (Pb 0))) (Ak (Pb 1)));
   Sd 2 (En (Dt 3) (Sk (Sv 4)))]
  [Dt 3]
  [Ch 2; Nm 1; Ak (Pb 0); Ik (Pb 1)]
  [Dt 3; Sk (Sv 4)].
