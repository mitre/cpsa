(** Protocol: bad-unilateral (bad_unilateral.scm:6:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (bad_unilateral.scm:7:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Send (bad_unilateral.scm:10:6) *)
   Bind (2, Text) (Frsh_);
   Bind (3, Mesg) (Encr_ 2 1);
   Send 0 3;
   (* Recv (bad_unilateral.scm:11:6) *)
   Bind (4, Text) (Recv_ 0);
   Same 4 2;
   Return [2]
  ].

(** Role: resp (bad_unilateral.scm:15:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Recv (bad_unilateral.scm:18:6) *)
   Bind (2, Mesg) (Recv_ 0);
   Bind (3, Text) (Decr_ 2 1);
   (* Send (bad_unilateral.scm:19:6) *)
   Send 0 3;
   Return [3]
  ].
