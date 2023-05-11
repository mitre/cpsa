(** Protocol: blanchet-fixed (blanchet.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (blanchet.scm:4:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Ikey); (3, Akey)]
  [
   (* Send (blanchet.scm:7:6) *)
   Bind (4, Skey) (Frsh_);
   Bind (5, Mesg) (Pair_ 4 1);
   Bind (6, Mesg) (Encr_ 5 2);
   Bind (7, Mesg) (Encr_ 6 3);
   Send 0 7;
   (* Recv (blanchet.scm:8:6) *)
   Bind (8, Mesg) (Recv_ 0);
   Bind (9, Data) (Decr_ 8 4);
   Return [9; 4]
  ].

(** Role: resp (blanchet.scm:12:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Akey); (3, Ikey)]
  [
   (* Recv (blanchet.scm:15:6) *)
   Bind (4, Mesg) (Recv_ 0);
   Bind (5, Mesg) (Decr_ 4 3);
   Bind (6, Mesg) (Decr_ 5 2);
   Bind (7, Skey) (Frst_ 6);
   Bind (8, Name) (Scnd_ 6);
   Same 8 1;
   (* Send (blanchet.scm:16:6) *)
   Bind (9, Data) (Frsh_);
   Bind (10, Mesg) (Encr_ 9 7);
   Send 0 10;
   Return [9; 7]
  ].
