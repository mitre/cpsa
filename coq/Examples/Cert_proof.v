(** * Cert Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Cert Cert_role.

Theorem correct_cert_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_cert_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.
