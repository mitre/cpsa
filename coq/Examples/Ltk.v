(** Protocol: ltk (ltk.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (ltk.scm:4:3) *)

Definition rho: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (ltk.scm:7:6) *)
   Bind (2, Mesg) (Recv_ 0);
   Bind (3, Mesg) (Decr_ 2 1);
   Bind (4, Name) (Frst_ 3);
   Bind (5, Mesg) (Scnd_ 3);
   Bind (6, Name) (Frst_ 5);
   Bind (7, Skey) (Scnd_ 5);
   Ltkp 7 4 6;
   (* Send (ltk.scm:8:6) *)
   Bind (8, Mesg) (Pair_ 4 6);
   Bind (9, Mesg) (Encr_ 8 7);
   Send 0 9;
   Return []
  ].
