(** Protocol: otway-rees (otway_rees.scm:7:1) *)

Require Import String List Alg Sem.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (otway_rees.scm:9:3) *)

Definition init_role: role :=
  mkRole
  [Sd 4 (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
   Rv 4 (En (Pr (Tx 3) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
            (Sk (Lt 0 5)))]
  [Tx 3]
  [Ch 4; Nm 0; Nm 1; Sk (Lt 0 5)]
  [Sk (Sv 2)].

(** Role: resp (otway_rees.scm:20:3) *)

Definition resp_role: role :=
  mkRole
  [Rv 6 (Pr (Nm 0) (Pr (Nm 1) (Tx 3)));
   Sd 7 (Pr (Nm 0) (Pr (Nm 1) (Pr (Tx 3) (Tx 4))));
   Rv 7 (Pr (Mg 5)
            (En (Pr (Tx 4) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
                (Sk (Lt 1 8))));
   Sd 6 (Mg 5)]
  [Tx 4]
  [Ch 6; Ch 7; Nm 1; Sk (Lt 1 8)]
  [Nm 0; Sk (Sv 2)].

(** Role: serv (otway_rees.scm:34:3) *)

Definition serv_role: role :=
  mkRole
  [Rv 5 (Pr (Nm 0) (Pr (Nm 1) (Pr (Tx 3) (Tx 4))));
   Sd 5 (Pr (En (Pr (Tx 3) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
                (Sk (Lt 0 6)))
            (En (Pr (Tx 4) (Pr (Nm 0) (Pr (Nm 1) (Sk (Sv 2)))))
                (Sk (Lt 1 6))))]
  [Sk (Sv 2)]
  [Ch 5; Nm 0; Nm 1; Sk (Lt 0 6); Sk (Lt 1 6)]
  [Sk (Sv 2)].
