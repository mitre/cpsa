(** Protocol: pubk2 (pubk2.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (pubk2.scm:4:3) *)

Definition rho: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (pubk2.scm:7:6) *)
   Bind (2, Aenc) (Recv_ 0);
   Bind (3, Pair) (Decr_ 2 1);
   Bind (4, Name) (Frst_ 3);
   Bind (5, Akey) (Scnd_ 3);
   Bind (6, Quot) (Quot_ "enc");
   Nm2p 5 6 4;
   (* Send (pubk2.scm:8:6) *)
   Bind (7, Aenc) (Encr_ 4 5);
   Send 0 7;
   Return []
  ].
