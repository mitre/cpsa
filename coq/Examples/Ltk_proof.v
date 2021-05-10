(** * Ltk Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Ltk Ltk_role.

Theorem correct_ltk_rho_io_liveness:
  correct_io_liveness rho_role rho.
Proof.
  sem_liveness.
Qed.

Theorem correct_ltk_rho_io_safety:
  correct_io_safety rho_role rho.
Proof.
  sem_safety.
Qed.
