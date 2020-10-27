(** * Yahalom Protocol Generated Code Verification *)

Require Import Sem SemTactics Yahalom Yahalom_role.

Theorem correct_yahalom_init_io_liveness:
  correct_io_liveness init_role init.
Proof.
  sem_liveness.
Qed.

Theorem correct_yahalom_resp_io_liveness:
  correct_io_liveness resp_role resp.
Proof.
  sem_liveness.
Qed.

Theorem correct_yahalom_serv_init_io_liveness:
  correct_io_liveness serv_init_role serv_init.
Proof.
  sem_liveness.
Qed.

Theorem correct_yahalom_serv_complete_io_liveness:
  correct_io_liveness serv_complete_role serv_complete.
Proof.
  sem_liveness.
Qed.

Theorem correct_yahalom_init_io_safety:
  correct_io_safety init_role init.
Proof.
  sem_safety.
Qed.

Theorem correct_yahalom_resp_io_safety:
  correct_io_safety resp_role resp.
Proof.
  sem_safety.
Qed.

Theorem correct_yahalom_serv_init_io_safety:
  correct_io_safety serv_init_role serv_init.
Proof.
  sem_safety.
Qed.

Theorem correct_yahalom_serv_complete_io_safety:
  correct_io_safety serv_complete_role serv_complete.
Proof.
  sem_safety.
Qed.
