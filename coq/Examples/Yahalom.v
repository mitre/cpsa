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
   Bind (5, Text) (Frsh_);
   Bind (6, Pair) (Pair_ 2 5);
   Send 0 6;
   (* Recv (yahalom.scm:14:6) *)
   Bind (7, Pair) (Recv_ 1);
   Bind (8, Senc) (Frst_ 7);
   Bind (9, Mesg) (Scnd_ 7);
   Bind (10, Pair) (Decr_ 8 4);
   Bind (11, Name) (Frst_ 10);
   Bind (12, Pair) (Scnd_ 10);
   Same 11 3;
   Bind (13, Skey) (Frst_ 12);
   Bind (14, Pair) (Scnd_ 12);
   Bind (15, Text) (Frst_ 14);
   Bind (16, Text) (Scnd_ 14);
   Same 15 5;
   (* Send (yahalom.scm:15:6) *)
   Bind (17, Senc) (Encr_ 16 13);
   Bind (18, Pair) (Pair_ 9 17);
   Send 0 18;
   Return [13]
  ].

(** Role: resp (yahalom.scm:23:3) *)

Definition resp: proc :=
  mkProc
  [(0, Chan); (1, Chan); (2, Name); (3, Skey)]
  [
   (* Recv (yahalom.scm:26:6) *)
   Bind (4, Pair) (Recv_ 0);
   Bind (5, Name) (Frst_ 4);
   Bind (6, Text) (Scnd_ 4);
   (* Send (yahalom.scm:27:6) *)
   Bind (7, Text) (Frsh_);
   Bind (8, Pair) (Pair_ 6 7);
   Bind (9, Pair) (Pair_ 5 8);
   Bind (10, Senc) (Encr_ 9 3);
   Bind (11, Pair) (Pair_ 2 10);
   Send 1 11;
   (* Recv (yahalom.scm:28:6) *)
   Bind (12, Pair) (Recv_ 0);
   Bind (13, Senc) (Frst_ 12);
   Bind (14, Senc) (Scnd_ 12);
   Bind (15, Pair) (Decr_ 13 3);
   Bind (16, Name) (Frst_ 15);
   Bind (17, Skey) (Scnd_ 15);
   Same 16 5;
   Bind (18, Text) (Decr_ 14 17);
   Same 18 7;
   Return [5; 17]
  ].

(** Role: serv-init (yahalom.scm:36:3) *)

Definition serv_init: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Skey)]
  [
   (* Recv (yahalom.scm:39:6) *)
   Bind (3, Pair) (Recv_ 0);
   Bind (4, Name) (Frst_ 3);
   Bind (5, Senc) (Scnd_ 3);
   Same 4 1;
   Bind (6, Pair) (Decr_ 5 2);
   Bind (7, Name) (Frst_ 6);
   Bind (8, Pair) (Scnd_ 6);
   Bind (9, Text) (Frst_ 8);
   Bind (10, Text) (Scnd_ 8);
   Return [7; 9; 10]
  ].

(** Role: serv-complete (yahalom.scm:45:3) *)

Definition serv_complete: proc :=
  mkProc
  [(0, Chan); (1, Name); (2, Name); (3, Skey); (4, Skey); (5, Text); (6, Text)]
  [
   (* Send (yahalom.scm:48:6) *)
   Bind (7, Skey) (Frsh_);
   Bind (8, Pair) (Pair_ 5 6);
   Bind (9, Pair) (Pair_ 7 8);
   Bind (10, Pair) (Pair_ 2 9);
   Bind (11, Senc) (Encr_ 10 3);
   Bind (12, Pair) (Pair_ 1 7);
   Bind (13, Senc) (Encr_ 12 4);
   Bind (14, Pair) (Pair_ 11 13);
   Send 0 14;
   Return [7]
  ].
