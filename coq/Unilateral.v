(** Protocol: unilateral (../rtst/unilateral.scm:5:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (../rtst/unilateral.scm:6:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Send (../rtst/unilateral.scm:9:7) *)
   Bind (2, Text) (Nonce);
   Bind (3, Mesg) (Encr 2 1);
   Send 0 3;
   (* Recv (../rtst/unilateral.scm:10:7) *)
   Bind (4, Text) (Recv 0);
   Same 4 2;
   Return [2]
  ].

(** Role: resp (../rtst/unilateral.scm:14:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (../rtst/unilateral.scm:17:7) *)
   Bind (2, Mesg) (Recv 0);
   Bind (3, Text) (Decr 2 1);
   (* Send (../rtst/unilateral.scm:18:7) *)
   Send 0 3;
   Return [3]
  ].
