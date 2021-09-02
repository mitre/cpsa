(** Protocol: nsl (nsl.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (nsl.scm:4:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Ikey); (2, Akey); (3, Akey)]
  [
   (* Send (nsl.scm:7:6) *)
   Bind (4, Text) (Frsh_);
   Bind (5, Mesg) (Pair_ 4 2);
   Bind (6, Mesg) (Encr_ 5 3);
   Send 0 6;
   (* Recv (nsl.scm:8:6) *)
   Bind (7, Mesg) (Recv_ 0);
   Bind (8, Mesg) (Decr_ 7 1);
   Bind (9, Text) (Frst_ 8);
   Bind (10, Mesg) (Scnd_ 8);
   Same 9 4;
   Bind (11, Text) (Frst_ 10);
   Bind (12, Akey) (Scnd_ 10);
   Same 12 3;
   (* Send (nsl.scm:9:6) *)
   Bind (13, Mesg) (Encr_ 11 3);
   Send 0 13;
   Return [4; 11]
  ].

(** Role: resp (nsl.scm:13:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Ikey); (2, Akey); (3, Akey)]
  [
   (* Recv (nsl.scm:16:6) *)
   Bind (4, Mesg) (Recv_ 0);
   Bind (5, Mesg) (Decr_ 4 1);
   Bind (6, Text) (Frst_ 5);
   Bind (7, Akey) (Scnd_ 5);
   Same 7 3;
   (* Send (nsl.scm:17:6) *)
   Bind (8, Text) (Frsh_);
   Bind (9, Mesg) (Pair_ 8 2);
   Bind (10, Mesg) (Pair_ 6 9);
   Bind (11, Mesg) (Encr_ 10 3);
   Send 0 11;
   (* Recv (nsl.scm:18:6) *)
   Bind (12, Mesg) (Recv_ 0);
   Bind (13, Text) (Decr_ 12 1);
   Same 13 8;
   Return [8; 6]
  ].
