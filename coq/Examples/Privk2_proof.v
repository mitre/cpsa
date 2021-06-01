(** * Privk2 Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Privk2 Privk2_role.

Theorem correct_privk2_rho_io_liveness:
  correct_io_liveness rho_role rho.
Proof.
  sem_liveness.
Qed.

Theorem correct_privk2_rho_io_safety:
  correct_io_safety rho_role rho.
Proof.
  sem_safety.
Qed.
