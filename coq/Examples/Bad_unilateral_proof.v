(** * Bad Unilateral Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Nsl Nsl_role.

Theorem correct_bad_unilateral_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_bad_unilateral_resp_io_liveness:
  correct_io_liveness resp_role resp.
Proof.
  sem_liveness.
Qed.

Theorem correct_bad_unilateral_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.

Theorem correct_bad_unilateral_resp_io_safety:
  correct_io_safety resp_role resp.
Proof.
  sem_safety.
Qed.
