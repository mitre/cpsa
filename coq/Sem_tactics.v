Require Import Alg Sem.

(** Some general purpose tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac find_if :=
  match goal with
  | [ |- context[ if ?X then _ else _ ] ] => destruct X
  end.

Ltac destruct_disjunct :=
  match goal with
  | [ H: _ \/ _  |- _ ] => destruct H as [H|H]
  end.

Ltac destruct_ex_and :=
  match goal with
  | [ H: _ /\ _ |- _ ] =>
    destruct H
  | [ H: exists _, _ |- _ ] =>
    destruct H
  end.

(** A tactic for running an execution *)

Ltac sem_auto :=
  repeat (econstructor; simpl; eauto).

(** A tactic proving liveness *)

Ltac sem_liveness :=
  apply correct_io_liveness_aid;
  eexists; eexists; eexists; split; eauto;
  split; sem_auto;
  let H := fresh "H" in
  unfold homomorphism; simpl; intro H; inv H.

(** This tactic handles input checks in a hypothesis. *)

Ltac sem_inputs :=
  repeat
    match goal with
    | [ H: type_check _ _ |- _ ] => inv H
    | [ H: ins_inputs _ _ |- _ ] => inv H
    end.

(** A semantics specific tactic for performing inversions *)

Ltac sem_inv :=
  repeat
    match goal with
    | [ H: Some _ = Some _ |- _ ] => inv H
    | [ H: ?l = inv ?r |- _ ] =>
      apply inv_swap in H; simpl in H; subst
    | [ H: lookup _ _ = _ |- _ ] => inv H
    | [ H: type_check _ _ |- _ ] => inv H
    | [ H: expr_sem _ _ _ _ _ _ _ |- _ ] => inv H
    | [ H: stmt_sem _ _ _ _ _ _ _ |- _ ] => inv H
    | [ H: stmt_list_sem _ _ _ _ _ _ _ _ |- _ ] => inv H
    end.

Ltac sem_rewrite :=
  repeat
    match goal with
    | [ H: _ = _ _ |- _ ] => rewrite <- H
    end.

(** Perform a safety proof. *)

Ltac sem_safety :=
  unfold correct_io_safety;
  intros ev ex E H;
  inv H;
  rewrite <- E in *;
  sem_inputs;
  sem_inv;
  simpl in *;
  sem_inv;
  unfold homomorphism;
  sem_rewrite;
  clear;
  simpl;
  unfold match_evt; simpl;
  unfold match_uniqs; simpl;
  unfold match_skey; simpl;
  unfold match_akey; simpl;
  unfold extend_term; simpl;
  repeat (find_if; simpl; auto);
  let H := fresh "H" in
  intro H;
  inv H.
