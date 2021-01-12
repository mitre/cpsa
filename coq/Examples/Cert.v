(** Protocol: cert (cert.scm:1:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (cert.scm:2:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Akey); (2, Mesg)]
  [
   Bind (3, Text) (Decr 2 1);
   (* Send (cert.scm:4:12) *)
   Send 0 2;
   Return []  ].
