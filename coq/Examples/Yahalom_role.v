(** Protocol: yahalom (yahalom.scm:7:1) *)

Require Import String List Alg Role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (yahalom.scm:9:3) *)

Definition init_role: role :=
  mkRole
  [Sd 6 (Pr (Nm 0) (Tx 3));
   Rv 7 (Pr (En (Pr (Nm 1) (Pr (Sk (Sv 2)) (Pr (Tx 3) (Tx 4))))
                (Sk (Lt 0 8))) (Mg 5));
   Sd 6 (Pr (Mg 5) (En (Tx 4) (Sk (Sv 2))))]
  [Tx 3]
  [Ch 6; Ch 7; Nm 0; Nm 1; Sk (Lt 0 8)]
  [Sk (Sv 2)].

(** Role: resp (yahalom.scm:23:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 5 (Pr (Nm 0) (Tx 3));
   Sd 6 (Pr (Nm 1) (En (Pr (Nm 0) (Pr (Tx 3) (Tx 4))) (Sk (Lt 1 7))));
   Rv 5 (Pr (En (Pr (Nm 0) (Sk (Sv 2))) (Sk (Lt 1 7)))
            (En (Tx 4) (Sk (Sv 2))))]
  [Tx 4]
  [Ch 5; Ch 6; Nm 1; Sk (Lt 1 7)]
  [Nm 0; Sk (Sv 2)].

(** Role: serv-init (yahalom.scm:36:3) *)

Definition serv_init_role: role :=
  mkRole
  [Rv 4 (Pr (Nm 1) (En (Pr (Nm 0) (Pr (Tx 2) (Tx 3))) (Sk (Lt 1 5))))]
  []
  [Ch 4; Nm 1; Sk (Lt 1 5)]
  [Nm 0; Tx 2; Tx 3].

(** Role: serv-complete (yahalom.scm:45:3) *)

Definition serv_complete_role: role :=
  mkRole
  [Sd 5 (Pr (En (Pr (Nm 1) (Pr (Sk (Sv 2)) (Pr (Tx 3) (Tx 4))))
                (Sk (Lt 0 6)))
            (En (Pr (Nm 0) (Sk (Sv 2))) (Sk (Lt 1 6))))]
  [Sk (Sv 2)]
  [Ch 5; Nm 0; Nm 1; Sk (Lt 0 6); Sk (Lt 1 6); Tx 3; Tx 4]
  [Sk (Sv 2)].
