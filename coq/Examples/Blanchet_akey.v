(** Protocol: blanchet-akey-fixed (blanchet_akey.scm:3:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (blanchet_akey.scm:4:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Akey); (2, Ikey)]
  [
   (* Send (blanchet_akey.scm:7:6) *)
   Bind (3, Skey) (Frsh_);
   Bind (4, Mesg) (Pair_ 1 3);
   Bind (5, Mesg) (Encr_ 4 2);
   Bind (6, Mesg) (Encr_ 5 1);
   Send 0 6;
   (* Recv (blanchet_akey.scm:8:6) *)
   Bind (7, Mesg) (Recv_ 0);
   Bind (8, Data) (Decr_ 7 3);
   Return [8; 3]
  ].

(** Role: resp (blanchet_akey.scm:12:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Akey); (2, Ikey)]
  [
   (* Recv (blanchet_akey.scm:15:6) *)
   Bind (3, Mesg) (Recv_ 0);
   Bind (4, Mesg) (Decr_ 3 2);
   Bind (5, Mesg) (Decr_ 4 1);
   Bind (6, Akey) (Frst_ 5);
   Bind (7, Skey) (Scnd_ 5);
   Invp 6 2;
   (* Send (blanchet_akey.scm:16:6) *)
   Bind (8, Data) (Frsh_);
   Bind (9, Mesg) (Encr_ 8 7);
   Send 0 9;
   Return [8; 7]
  ].
