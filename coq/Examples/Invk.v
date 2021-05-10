(** Protocol: invk (invk.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: rho (invk.scm:4:3) *)

Definition rho: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Recv (invk.scm:7:6) *)
   Bind (2, Pair) (Recv_ 0);
   Bind (3, Name) (Frst_ 2);
   Bind (4, Ikey) (Scnd_ 2);
   Invp 4 1;
   (* Send (invk.scm:8:6) *)
   Bind (5, Aenc) (Encr_ 3 1);
   Send 0 5;
   Return []
  ].
