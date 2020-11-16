(** * Otway Rees Protocol Generated Code Verification *)

Require Import Sem Sem_tactics Otway_rees Otway_rees_role.

Theorem correct_otway_rees_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_otway_rees_resp_io_liveness:
  correct_io_liveness resp_role resp.
Proof.
  sem_liveness.
Qed.

Theorem correct_otway_rees_serv_io_liveness:
  correct_io_liveness serv_role serv.
Proof.
  sem_liveness.
Qed.

Theorem correct_otway_rees_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.

Theorem correct_otway_rees_resp_io_safety:
  correct_io_safety resp_role resp.
Proof.
  sem_safety.
Qed.

Theorem correct_otway_rees_serv_io_safety:
  correct_io_safety serv_role serv.
Proof.
  sem_safety.
Qed.
