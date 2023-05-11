(** * Blanchet Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Blanchet Blanchet_role.

Theorem correct_blanchet_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_blanchet_resp_io_liveness:
  correct_io_liveness resp_role resp.
Proof.
  sem_liveness.
Qed.

Theorem correct_blanchet_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.

Theorem correct_blanchet_resp_io_safety:
  correct_io_safety resp_role resp.
Proof.
  sem_safety.
Qed.
