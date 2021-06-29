(** Protocol: unilateral (unilateral.scm:5:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (unilateral.scm:6:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Send (unilateral.scm:9:7) *)
   Bind (2, Text) (Frsh_);
   Bind (3, Mesg) (Encr_ 2 1);
   Send 0 3;
   (* Recv (unilateral.scm:10:7) *)
   Bind (4, Text) (Recv_ 0);
   Same 4 2;
   Return [2]
  ].

(** Role: resp (unilateral.scm:14:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (unilateral.scm:17:7) *)
   Bind (2, Mesg) (Recv_ 0);
   Bind (3, Text) (Decr_ 2 1);
   (* Send (unilateral.scm:18:7) *)
   Send 0 3;
   Return [3]
  ].
