(* Nonce Generation Order

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * Nonce Generation Order

    This library defines a function that computes the correct order
    for generating nonces during a run of a procedure.  It makes sure
    that basic values that uniquely originate are generated just
    before the transmission of the message in which they originate. *)

Require Import FunInd Bool Preamble Monad Proc Alg Role Sem Run Run_sem.
(** printing <- #←# *)

(** Find a nonce [u] of type [t] that is carried by [x].  Remove [u]
    from the list of uniquely originating values. *)

Fixpoint find_nonce (x: alg) (t: type) (acc: list alg) (us: list alg):
  option (alg * list alg) :=
  match us with
  | nil => None
  | u :: us =>
    if type_eqb t (type_of u) && cb u x then
      Some (u, rev acc ++ us)
    else
      find_nonce x t (u :: acc) us
  end.

(** Return a list of correctly ordered generated nonces if it exists. *)

Fixpoint nonce (stmts: list stmt) (tr: list evt) (us: list alg):
  option (list alg) :=
  match stmts, tr with
  | nil, _ => None
  | Return _ :: _, nil =>
    match us with
    | nil => Some nil
    | _ => None
    end
  | Bind (_, t) Frsh_ :: stmts, Sd _ x :: _ =>
    p <- find_nonce x t nil us;;
    let (u, us) := p in
    us <- nonce stmts tr us;;
    Some (u :: us)
  | Bind (_, _) Frsh_ :: stmts, Rv _ _ :: _ =>
    None
  | Send _ _ :: stmts, Sd _ x :: tr =>
    if existsb (fun u => cb u x) us then
      None
    else
      nonce stmts tr us
  | Send _ _ :: _, Rv _ _ :: _ => None
  | Bind _ (Recv_ _) :: stmts, Rv _ _ :: tr =>
    nonce stmts tr us
  | Bind _ (Recv_ _) :: _, Sd _ _ :: _ =>  None
  | _ :: stmts, tr => nonce stmts tr us
  end.

(** Compute the correct nonce order and use it to execute the procedure. *)

Definition run_nonce (p: proc) (ins: list alg) (tr: list evt)
           (us: list alg): option (env * list alg) :=
  us <- nonce (body p) tr us;;
  run p ins tr us.

Functional Scheme find_nonce_ind :=
  Induction for find_nonce Sort Prop.

Lemma found_nonces_preserved:
  forall x t acc us u us',
    find_nonce x t acc us = Some (u, us') ->
    incl (rev acc ++ us) (u :: us') /\  incl (u :: us') (rev acc ++ us).
Proof.
  intros x t acc us.
  functional induction (find_nonce x t acc us); intros.
  - inv H.
  - inv H.
    split; unfold incl; intros; simpl; rewrite in_app_iff; simpl.
    + apply in_app_iff in H; destruct H; auto.
      apply in_inv in H; intuition.
    + apply in_inv in H; intuition.
      apply in_app_iff in H0; destruct H0; auto.
  - apply IHo in H.
    simpl in H.
    rewrite <- app_assoc in H.
    simpl in H; intuition.
Qed.

Functional Scheme nonce_ind :=
  Induction for nonce Sort Prop.

(** The [nonces] function preserves the nonces when it succeeds. *)

Lemma nonces_preserved:
  forall stmts tr us,
    match nonce stmts tr us with
    | None => True
    | Some us' => incl us' us /\ incl us us'
    end.
Proof.
  intros.
  functional induction (nonce stmts tr us); auto.
  - split; apply incl_nil_l.
  - rewrite e9 in IHo; destruct IHo.
    apply found_nonces_preserved in e7.
    simpl in e7.
    destruct e7.
    split; unfold incl; intros.
    + apply H2; simpl.
      apply in_inv in H3; intuition.
    + apply H1 in H3.
      apply in_inv in H3; intuition auto with *; subst; simpl; auto.
Qed.

(** An easily computed condition for a compiler source target pair to
    be correct. *)

Definition correct_source_target_pair (rl: role) (p: proc): Prop :=
  valid_role rl = true /\
  match run_nonce p (inputs rl) (trace rl) (uniqs rl) with
  | Some (_, outs) => outs = outputs rl
  | None => False
  end.

(** The proof script that performs the proof. *)

Ltac correct_source_target_pair_proof :=
  unfold correct_source_target_pair;
  compute; auto.

(** A run using the correct nonce ordering satisfies the semantics. *)

Theorem run_nonce_sem:
  forall p rl us ev,
    nonce (body p) (trace rl) (uniqs rl) = Some us ->
    run p (inputs rl) (trace rl) us = Some (ev, outputs rl) ->
    sem p ev (mkRole
                (trace rl)
                us
                (inputs rl)
                (outputs rl)).
Proof.
  unfold run.
  intros.
  unfold sem.
  simpl.
  apply do_some in H0.
  destruct H0 as [ev' G].
  destruct G.
  apply sem_ins_inputs in H0.
  destruct H0; subst; split; auto.
  rewrite rev_involutive in H1.
  apply run_stmts_implies_stmt_list_sem in H1.
  simpl in H1; auto.
Qed.

(** This conjecture is likely true, but lemmas about homomophisms
    needed to complete the proof have not been proved. *)

Conjecture correct_source_target_pair_io_liveness:
  forall rl p,
    correct_source_target_pair rl p ->
    correct_io_liveness rl p.
