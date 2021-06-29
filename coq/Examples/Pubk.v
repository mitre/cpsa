(** Protocol: pubk (pubk.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (pubk.scm:4:3) *)

Definition rho: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (pubk.scm:7:6) *)
   Bind (2, Mesg) (Recv_ 0);
   Bind (3, Mesg) (Decr_ 2 1);
   Bind (4, Name) (Frst_ 3);
   Bind (5, Akey) (Scnd_ 3);
   Namp 5 4;
   (* Send (pubk.scm:8:6) *)
   Bind (6, Mesg) (Encr_ 4 5);
   Send 0 6;
   Return []
  ].
