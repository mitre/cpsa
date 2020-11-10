(** Protocol: yahalom (yahalom.scm:7:1) *)

Require Import Proc.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string.

(** Role: init (yahalom.scm:9:3) *)

Definition init: proc :=
  mkProc
  [(0, Chan); (1, Chan); (2, Name); (3, Name); (4, Skey)]
  [
   (* Send (yahalom.scm:13:6) *)
   Bind (5, Text) (Nonce);
   Bind (6, Mesg) (Pair 2 5);
   Send 0 6;
   (* Recv (yahalom.scm:14:6) *)
   Bind (7, Mesg) (Recv 1);
   Bind (8, Mesg) (Frst 7);
   Bind (9, Mesg) (Scnd 7);
   Bind (10, Mesg) (Decr 8 4);
   Bind (11, Name) (Frst 10);
   Bind (12, Mesg) (Scnd 10);
   Same 11 3;
   Bind (13, Skey) (Frst 12);
   Bind (14, Mesg) (Scnd 12);
   Bind (15, Text) (Frst 14);
   Bind (16, Text) (Scnd 14);
   Same 15 5;
   (* Send (yahalom.scm:15:6) *)
   Bind (17, Mesg) (Encr 16 13);
   Bind (18, Mesg) (Pair 9 17);
   Send 0 18;
   Return [13]
  ].

(** Role: resp (yahalom.scm:23:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Chan); (2, Name); (3, Skey)]
  [
   (* Recv (yahalom.scm:26:6) *)
   Bind (4, Mesg) (Recv 0);
   Bind (5, Name) (Frst 4);
   Bind (6, Text) (Scnd 4);
   (* Send (yahalom.scm:27:6) *)
   Bind (7, Text) (Nonce);
   Bind (8, Mesg) (Pair 6 7);
   Bind (9, Mesg) (Pair 5 8);
   Bind (10, Mesg) (Encr 9 3);
   Bind (11, Mesg) (Pair 2 10);
   Send 1 11;
   (* Recv (yahalom.scm:28:6) *)
   Bind (12, Mesg) (Recv 0);
   Bind (13, Mesg) (Frst 12);
   Bind (14, Mesg) (Scnd 12);
   Bind (15, Mesg) (Decr 13 3);
   Bind (16, Name) (Frst 15);
   Bind (17, Skey) (Scnd 15);
   Same 16 5;
   Bind (18, Text) (Decr 14 17);
   Same 18 7;
   Return [5; 17]
  ].

(** Role: serv-init (yahalom.scm:36:3) *)

Definition serv_init: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Skey)]
  [
   (* Recv (yahalom.scm:39:6) *)
   Bind (3, Mesg) (Recv 0);
   Bind (4, Name) (Frst 3);
   Bind (5, Mesg) (Scnd 3);
   Same 4 1;
   Bind (6, Mesg) (Decr 5 2);
   Bind (7, Name) (Frst 6);
   Bind (8, Mesg) (Scnd 6);
   Bind (9, Text) (Frst 8);
   Bind (10, Text) (Scnd 8);
   Return [7; 9; 10]
  ].

(** Role: serv-complete (yahalom.scm:45:3) *)

Definition serv_complete: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Name); (3, Skey); (4, Skey); (5, Text); (6, Text)]
  [
   (* Send (yahalom.scm:48:6) *)
   Bind (7, Skey) (Nonce);
   Bind (8, Mesg) (Pair 5 6);
   Bind (9, Mesg) (Pair 7 8);
   Bind (10, Mesg) (Pair 2 9);
   Bind (11, Mesg) (Encr 10 3);
   Bind (12, Mesg) (Pair 1 7);
   Bind (13, Mesg) (Encr 12 4);
   Bind (14, Mesg) (Pair 11 13);
   Send 0 14;
   Return [7]
  ].
