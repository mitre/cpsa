(** * Unilateral Protocol Generated Code Verification *)

Require Import List Program Monad Proc Alg.
Require Import Sem Sem_tactics Unilateral Unilateral_role.
Import List.ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

Lemma init_valid:
  valid_role init_role = true.
Proof.
  simpl; auto.
Qed.

(** This shows the expected execution is a run of the [init] procedure. *)

Theorem unilateral_init:
  exists ev,
    sem init ev init_role.
Proof.
  eexists.
  unfold sem; simpl; split; auto.
  sem_auto.
Qed.

Lemma resp_valid:
  valid_role resp_role = true.
Proof.
  simpl; auto.
Qed.

(** This shows the expected execution is a run of the [resp] procedure. *)

Theorem unilateral_resp:
  exists ev,
    sem resp ev resp_role.
Proof.
  eexists.
  unfold sem; simpl; split; auto.
  sem_auto.
Qed.

(** ** Correct Input/Output *)

Theorem correct_unilateral_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_unilateral_resp_io_liveness:
  correct_io_liveness resp_role resp.
Proof.
  sem_liveness.
Qed.

Theorem correct_unilateral_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.

Theorem correct_unilateral_resp_io_safety:
  correct_io_safety resp_role resp.
Proof.
  sem_safety.
Qed.

(** ** Bad Init

    The section shows what can go wrong when an input/output pair
    has a bad output.

    This version of init fails to make a sameness check. *)

Definition bad_init: proc :=
  mkProc
  [(0, Chan); (1, Akey)]
  [
   (* Send (rtst/unilateral.scm:9:7) *)
   Bind (2, Text) (Nonce_);
   Bind (3, Aenc) (Encr_ 2 1);
   Send 0 3;
   (* Recv (rtst/unilateral.scm:10:7) *)
   Bind (4, Text) (Recv_ 0);
   Return [2]
  ].

(** Liveness is okay. *)

Theorem correct_unilateral_bad_init_io_liveness:
  correct_io_liveness init_role bad_init.
Proof.
  sem_liveness.
Qed.

Definition bad_init_role: role :=
  mkRole
  [Sd 0 (En (Tx 2) (Ak (Av 1))); Rv 0 (Tx 3)]
  [Tx 2]
  [Ch 0; Ak (Av 1)]
  [Tx 2].

Lemma unilateral_bad_init:
  exists ev,
    sem bad_init ev bad_init_role.
Proof.
  eexists.
  unfold sem; simpl; split; auto.
  sem_auto.
Qed.

(** Safety fails. *)

Theorem correct_unilateral_bad_init_io_safety:
  ~(correct_io_safety init_role bad_init).
Proof.
  intro.
  unfold correct_io_safety in H.
  pose proof unilateral_bad_init as G.
  destruct G as [ev G].
  apply H in G; simpl; auto.
Qed.

(** The good version of [init] does not allow a [bad_init_role] run. *)

Lemma bad_init_fails_good_proc:
  forall ev,
    ~sem init ev bad_init_role.
Proof.
  intro.
  intro.
  unfold sem in H.
  destruct H as [G H].
  sem_inv.
Qed.
