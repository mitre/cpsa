(** Protocol: blanchet-akey-fixed (blanchet_akey.scm:3:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (blanchet_akey.scm:4:3) *)

Definition init_role: role :=
  mkRole
  [Sd 2 (En (En (Pr (Ak (Av 1)) (Sk (Sv 4))) (Ik (Av 0))) (Ak (Av 1)));
   Rv 2 (En (Dt 3) (Sk (Sv 4)))]
  [Sk (Sv 4)]
  [Ch 2; Ak (Av 1); Ik (Av 0)]
  [Dt 3; Sk (Sv 4)].

(** Role: resp (blanchet_akey.scm:12:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 2 (En (En (Pr (Ak (Av 1)) (Sk (Sv 4))) (Ik (Av 0))) (Ak (Av 1)));
   Sd 2 (En (Dt 3) (Sk (Sv 4)))]
  [Dt 3]
  [Ch 2; Ak (Av 0); Ik (Av 1)]
  [Dt 3; Sk (Sv 4)].
