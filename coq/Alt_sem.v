(* Alternate Abstract Execution Semantics

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * An Alternate Abstract Execution Semantics

    This section provides a semantics for produres using traces and
    unique lists instead of execution.  See [sem'].  Some people might
    find this definition more intuitive. *)

Require Import FunInd Program Arith Lia.
Require Import Preamble Monad Proc Alg Sem.
Import List.ListNotations.
Open Scope list_scope.

(** Extract the inputs from a runtime environment. *)

Definition get_ins (ev: env) (ds: list decl): list alg :=
  map snd (skipn (length ev - length ds) ev).

Functional Scheme mk_env_ind :=
  Induction for mk_env Sort Prop.

Lemma ins_inputs_length:
  forall inputs ds,
    ins_inputs ds inputs ->
    length (mk_env ds inputs) = length ds.
Proof.
  intros.
  functional induction (mk_env ds inputs); auto.
  - inv H.
  - inv H; simpl.
    apply IHe in H6.
    rewrite H6; auto.
Qed.

Lemma get_ins_inputs:
  forall inputs ds ev,
    ins_inputs ds inputs ->
    get_ins (ev ++ mk_env ds inputs) ds = inputs.
Proof.
  intros.
  unfold get_ins.
  rewrite skipn_app.
  rewrite app_length.
  rewrite ins_inputs_length; auto.
  assert (G: length ev +
             length ds -
             length ds = length ev).
  lia.
  rewrite G.
  rewrite skipn_all.
  rewrite app_nil_l.
  rewrite minus_diag; simpl.
  clear G.
  induction H; simpl; auto.
  rewrite IHins_inputs; auto.
Qed.

(** Function [get_ins] gets the correct inputs. *)

Lemma sem_implies_inputs:
  forall (p: proc) (ev: env) (ex: role),
    sem p ev ex ->
    inputs ex = get_ins ev (ins p).
Proof.
  intros.
  destruct H.
  apply stmt_list_sem_env_extends in H0.
  destruct H0 as [ev']; subst.
  eapply get_ins_inputs in H; eauto.
Qed.

(** Get the outputs from a runtime environment and some statements. *)

Fixpoint get_outs (ev: env) (stmts: list stmt): option (list alg) :=
  match stmts with
  | [] => None
  | [Return vs] => map_m (flip lookup ev) vs
  | _ :: stmts => get_outs ev stmts
  end.

Functional Scheme get_outs_ind :=
  Induction for get_outs Sort Prop.

(** Function [get_outs] gets the correct outputs. *)

Lemma stmt_list_sem_implies_outputs:
  forall ev tr us outs stmts ev',
    stmt_list_sem ev tr us outs stmts ev' ->
    get_outs ev' stmts = Some outs.
Proof.
  intros.
  revert H.
  revert ev.
  revert tr.
  revert us.
  functional induction (get_outs ev' stmts); intros.
  - inv H.
  - inv H; auto.
    inv H6.
  - inv H.
    inv H6.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
  - inv H.
    apply IHo in H8; auto.
Qed.

Lemma sem_implies_outputs:
  forall (p: proc) (ev: env) (ex: role),
    sem p ev ex ->
    get_outs ev (body p) = Some (outputs ex).
Proof.
  intros.
  unfold sem in H.
  destruct H.
  clear H.
  apply stmt_list_sem_implies_outputs in H0; auto.
Qed.

(** The alternate abstract execution semantics for procedures *)

Definition sem' (p: proc) (ev: env) (tr: list evt) (us: list alg): Prop :=
  let inputs := get_ins ev (ins p) in
  let ev_in := mk_env (ins p) inputs in
  ins_inputs (ins p) inputs /\
  exists outs,
    get_outs ev (body p) = Some outs /\
    stmt_list_sem ev_in tr us outs (body p) ev.

Lemma sem_implies_sem':
  forall (p: proc) (ev: env) (ex: role),
    sem p ev ex ->
    sem' p ev (trace ex) (uniqs ex).
Proof.
  intros.
  pose proof H as G.
  apply sem_implies_inputs in G.
  pose proof H as F.
  apply sem_implies_outputs in F.
  unfold sem in H.
  destruct H as [E H].
  rewrite G in E.
  rewrite G in H.
  unfold sem'.
  split; auto.
  exists (outputs ex); split; auto.
Qed.

Lemma sem'_implies_sem:
  forall (p: proc) (ev: env) (tr: list evt) (us: list alg),
    sem' p ev tr us ->
    exists outs,
      get_outs ev (body p) = Some outs /\
      let ins := get_ins ev (ins p) in
      sem p ev (mkRole tr us ins outs).
Proof.
  intros.
  unfold sem' in H.
  destruct H.
  destruct H0 as [outs].
  exists outs.
  unfold sem; simpl; intuition.
Qed.
