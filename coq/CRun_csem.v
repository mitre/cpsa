(* Correctness of Concrete Run semantics

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** This library contains proofs that the semantics specified in
    [Roletran.Run] and [Roletran.Sem] agree. *)

Require Import FunInd List Bool Arith.
Require Import Preamble Proc Alg Role CSem CRun.
Open Scope nat_scope.

Lemma expr_csem_implies_crun_expr:
  forall ev tr us rs exp val tr' us' rs',
    expr_csem ev tr us rs exp val tr' us' rs' ->
    crun_expr (mkCRSt ev tr us rs) exp =
    Some (mkCRSt ev tr' us' rs', val).
Proof.
  intros.
  inv H; simpl;
    repeat match goal with
           | [ H: lookup _ _ = Some _ |- _ ] => rewrite H
           end; auto.
  - rewrite H2; simpl.
    destruct (bool_dec (calg_eqb (cinv b) (cinv b)) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite calg_eq_correct; auto.
  - rewrite Nat.eqb_refl; auto.
Qed.

Lemma crun_expr_implies_expr_csem:
  forall rst exp val rst',
    crun_expr rst exp = Some (rst', val) ->
    expr_csem (crenv rst) (crtr rst) (cruniqs rst) (crs rst)
              exp val (crtr rst') (cruniqs rst') (crs rst') /\
    crenv rst = crenv rst'.
Proof.
  intros.
  destruct exp; simpl in H.
  - inv H; simpl; auto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H; inv H; auto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct (option_dec (lookup n0 (crenv rst))) as [F|F].
      * rewrite F in H; inv H.
      * destruct F as [c F]; rewrite F in H; inv H; auto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct (option_dec (lookup n0 (crenv rst))) as [F|F].
      * rewrite F in H; inv H.
      * destruct F as [c F]; rewrite F in H; inv H; auto.
        pose proof destruct_list (crs rst) as E.
        destruct E.
        -- destruct s.
           destruct s.
           rewrite e in H1.
           inv H1; simpl; auto.
           rewrite e; auto.
        -- rewrite e in H1.
           inv H1.
           rewrite e; auto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      split; auto.
      eapply CExpr_frst; eauto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      split; auto.
      eapply CExpr_scnd; eauto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      destruct (option_dec (lookup n0 (crenv rst))) as [F|F].
      * rewrite F in H1; inv H1; destruct b; inv H0.
      * destruct F as [c F]; rewrite F in H1.
        destruct (alt_bool_dec (negb (chas_enc c))) as [D|D];
          rewrite D in H1; simpl in H1.
        destruct (bool_dec (calg_eqb c (cinv b2)) true) as [E|E].
        -- rewrite E in H1; inv H1.
           apply calg_eq_correct in E; subst.
           split; auto.
           eapply CExpr_decr; eauto.
           apply negb_true_iff in D; auto.
        -- rewrite not_true_iff_false in E.
           rewrite E in H1; inv H1.
        -- inv H1.
  - destruct (cruniqs rst); inv H; auto.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [c G]; rewrite G in H.
      destruct (crtr rst).
      * inv H.
      * destruct c0.
        -- inv H.
        -- destruct c; inv H.
           destruct (bool_dec (n1 =? n0) true) as [F|F].
           ++ rewrite F in H1; inv H1.
              apply Nat.eqb_eq in F; subst; auto.
           ++ rewrite not_true_iff_false in F.
              rewrite F in H1; inv H1.
Qed.

Lemma ctype_check_reflect:
  forall (x: calg) (t: type),
    ctype_check x t = true <-> CSem.ctype_check t x.
Proof.
  intros.
  unfold ctype_check.
  rewrite orb_true_iff.
  repeat rewrite type_eq_correct.
  split; intros; subst;
    destruct x; inversion H; subst; simpl; auto.
Qed.

Lemma stmt_csem_implies_crun_stmt:
  forall ev tr us rs cmd ev' tr' us' rs',
    stmt_csem ev tr us rs cmd ev' tr' us' rs' ->
    crun_stmt (mkCRSt ev tr us rs) cmd =
    Some (mkCRSt ev' tr' us' rs').
Proof.
  intros.
  inv H.
  - apply expr_csem_implies_crun_expr in H0.
    rewrite <- ctype_check_reflect in H1.
    simpl.
    rewrite H0.
    rewrite H1; auto.
  - simpl.
    rewrite H0.
    rewrite Nat.eqb_refl; auto.
    rewrite H1.
    destruct (bool_dec (calg_eqb a a) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite calg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    simpl.
    destruct (bool_dec (calg_eqb b b) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite calg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    simpl.
    destruct (bool_dec (calg_eqb (cinv b) (cinv b)) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite calg_eq_correct; auto.
Qed.

Lemma crun_stmt_implies_stmt_csem:
  forall rst cmd rst',
    crun_stmt rst cmd = Some rst' ->
    stmt_csem (crenv rst) (crtr rst) (cruniqs rst) (crs rst)
              cmd (crenv rst') (crtr rst') (cruniqs rst') (crs rst').
Proof.
  intros; destruct cmd; simpl in *.
  - inv H.
  - destruct d as [v t].
    destruct (option_dec (crun_expr rst e)) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G].
      destruct b as [st x].
      rewrite G in H.
      destruct (bool_dec (ctype_check x t) true) as [F|F].
      * rewrite F in H.
        inv H; simpl.
        rewrite ctype_check_reflect in F.
        apply crun_expr_implies_expr_csem in G; auto.
        destruct G.
        rewrite <- H0.
        eapply CStmt_bind; eauto.
      * rewrite not_true_iff_false in F.
        rewrite F in H; inv H.
  - destruct (crtr rst).
    + inv H.
    + destruct c.
      * destruct (option_dec (lookup n (crenv rst))) as [G|G].
        -- rewrite G in H; inv H.
        -- destruct G.
           rewrite H0 in H.
           destruct x; inv H.
           destruct (bool_dec (n2 =? n1) true) as [G|G].
           ++ rewrite G in H2; inv H2.
              apply Nat.eqb_eq in G; subst.
              destruct (option_dec (lookup n0 (crenv rst))) as [G|G].
              ** rewrite G in H1; inv H1.
              ** destruct G.
                 rewrite H in H1.
                 destruct (bool_dec (calg_eqb c x) true) as [F|F].
                 --- rewrite F in H1; inv H1.
                     rewrite calg_eq_correct in F; subst.
                     apply CStmt_send; auto.
                 --- rewrite not_true_iff_false in F.
                     rewrite F in H1; inv H1.
           ++ rewrite not_true_iff_false in G.
              rewrite G in H2; inv H2.
      * inv H.
  - destruct (option_dec (lookup n (crenv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G.
      rewrite H0 in H.
      destruct (option_dec (lookup n0 (crenv rst))) as [G|G].
      * rewrite G in H; inv H.
      * destruct G.
        rewrite H1 in H.
        destruct (alt_bool_dec (chas_enc x)) as [F|F];
          rewrite F in H; simpl in H.
        inv H.
        destruct (bool_dec (calg_eqb x x0) true) as [G|G].
        -- rewrite G in H; inv H.
           apply calg_eq_correct in G; subst.
           eapply CStmt_same; eauto.
        -- rewrite not_true_iff_false in G.
           rewrite G in H; inv H.
  - alt_option_dec (lookup n (crenv rst)) x G;
      rewrite G in H.
    + inv H.
    + alt_option_dec (lookup n0 (crenv rst)) y F;
        rewrite F in H.
      * inv H.
      * destruct (alt_bool_dec (chas_enc x)) as [D|D];
          rewrite D in H; simpl in H.
        inv H.
        destruct (alt_bool_dec (calg_eqb x (cinv y))) as [E|E];
          rewrite E in H.
        -- inv H.
           apply calg_eq_correct in E.
           eapply CStmt_invp; eauto.
        -- inv H.
Qed.

Lemma stmt_list_csem_implies_crun_stmts:
  forall ev_in tr us rs outs stmts ev,
    stmt_list_csem ev_in tr us rs outs stmts ev ->
    crun_stmts (mkCRSt ev_in tr us rs) stmts = Some (ev, outs).
Proof.
  intros.
  induction H.
  - unfold Basics.flip in H.
    simpl.
    rewrite H; auto.
  - apply stmt_csem_implies_crun_stmt in H.
    simpl; rewrite H.
    destruct stmt; simpl; simpl in H; auto.
    inv H.
Qed.

Functional Scheme crun_stmts_ind :=
  Induction for crun_stmts Sort Prop.

Lemma crun_stmts_implies_stmt_list_csem:
  forall rst stmts ev outs,
    crun_stmts rst stmts = Some (ev, outs) ->
    stmt_list_csem (crenv rst) (crtr rst) (cruniqs rst)
                   (crs rst) outs stmts ev.
Proof.
  intros.
  functional induction (crun_stmts rst stmts); inv H.
  - rewrite e2.
    rewrite e3.
    apply CStmt_return; auto.
  - inv e2.
  - apply crun_stmt_implies_stmt_csem in e1.
    apply IHo in H1.
    eapply CStmt_pair; eauto.
  - apply crun_stmt_implies_stmt_csem in e1.
    apply IHo in H1.
    eapply CStmt_pair; eauto.
  - apply crun_stmt_implies_stmt_csem in e1.
    apply IHo in H1.
    eapply CStmt_pair; eauto.
  - apply crun_stmt_implies_stmt_csem in e1.
    apply IHo in H1.
    eapply CStmt_pair; eauto.
Qed.

Lemma csem_bind_inputs_aux:
  forall ds xs ev,
    cins_inputs ds xs ->
    cbind_inputs ds xs ev = Some (rev (mk_cenv ds xs) ++ ev).
Proof.
  intros ds xs ev H.
  revert ev.
  induction H; intros; simpl; auto.
  rewrite <- ctype_check_reflect in H.
  rewrite H.
  rewrite IHcins_inputs; simpl; auto.
  repeat rewrite <- app_assoc.
  repeat rewrite rev_app_distr; simpl.
  simpl; auto.
Qed.

Lemma csem_bind_inputs:
  forall ds xs,
    cins_inputs ds xs ->
    cbind_inputs ds xs nil = Some (rev (mk_cenv ds xs)).
Proof.
  intros.
  rewrite csem_bind_inputs_aux; auto.
  rewrite app_nil_r; auto.
Qed.

Functional Scheme cbind_inputs_ind :=
  Induction for cbind_inputs Sort Prop.

Lemma csem_ins_inputs_aux:
  forall ds xs ev ev',
    cbind_inputs ds xs ev = Some ev' ->
    cins_inputs ds xs.
Proof.
  intros.
  functional induction (cbind_inputs ds xs ev); simpl; auto; inv H.
  apply ctype_check_reflect in e2.
  apply CIns_inputs_pair; auto.
Qed.

Lemma csem_ins_inputs:
  forall ds xs ev,
    cbind_inputs ds xs nil = Some ev ->
    cins_inputs ds xs /\ ev = rev (mk_cenv ds xs).
Proof.
  intros.
  assert (G: cins_inputs ds xs).
  - eapply csem_ins_inputs_aux; eauto.
  - split; auto.
    pose proof (csem_bind_inputs ds xs).
    apply H0 in G.
    rewrite G in H.
    inv H; auto.
Qed.

Lemma crun_inputs:
  forall (p: proc) (inputs: list calg) (rs: list nat) (cev: cenv)
         (ctr: list cevt) (cus couts: list calg),
    crun p inputs ctr cus rs = Some (cev, couts) ->
    inputs = mk_ins cev (ins p).
Proof.
  intros.
  unfold crun in H.
  alt_option_dec (cbind_inputs (ins p) inputs nil) renv G;
    rewrite G in H.
  - inv H.
  - apply csem_ins_inputs in G.
    destruct G; subst.
    rewrite rev_involutive in H.
    apply crun_stmts_env_extends in H.
    destruct H as [ev H].
    simpl in H; subst.
    rewrite mk_ins_inputs; auto.
Qed.

(** The semantics as a predicate implies the semantics as a function. *)

Theorem csem_implies_run:
  forall (p: proc) (rs: list nat) (cev: cenv) (e: role),
    csem p rs cev e ->
    exists (ctr: list cevt) (cus: list calg) (couts: list calg),
      crun p (mk_ins cev (ins p)) ctr cus rs = Some (cev, couts) /\
      trace e = map to_evt ctr /\
      uniqs e = map to_alg cus /\
      inputs e = map to_alg (mk_ins cev (ins p)) /\
      outputs e = map to_alg couts.
Proof.
  intros.
  apply csem_csem' in H.
  unfold csem' in H.
  destruct H.
  destruct H0.
  destruct H1 as [ctr].
  exists ctr.
  destruct H1 as [cus].
  exists cus.
  destruct H1.
  destruct H2.
  destruct H3 as [couts].
  exists couts.
  repeat destruct_ex_and.
  apply stmt_list_csem_implies_crun_stmts in H4.
  simpl in H4.
  apply csem_bind_inputs in H0.
  unfold crun.
  rewrite H0.
  rewrite rev_involutive.
  auto.
Qed.

(** The semantics as a function implies the semantics as a predicate. *)

Theorem run_implies_csem:
  forall (p: proc) (inputs: list calg) (rs: list nat) (cev: cenv)
         (ctr: list cevt) (cus couts: list calg),
    crun p inputs ctr cus rs = Some (cev, couts) ->
    csem p rs cev
         (mkRole (map to_evt ctr)
                 (map to_alg cus)
                 (map to_alg inputs)
                 (map to_alg couts)).
Proof.
  intros.
  pose proof H as A.
  apply crun_inputs in A.
  subst.
  unfold crun in H.
  alt_option_dec (cbind_inputs (ins p) (mk_ins cev (ins p)) nil) renv G;
    rewrite G in H.
  - inv H.
  - apply csem_ins_inputs in G.
    destruct G; subst.
    rewrite rev_involutive in H.
    apply crun_stmts_implies_stmt_list_csem in H; simpl in H.
    apply csem'_csem.
    unfold csem'.
    simpl.
    split; auto.
    split; auto.
    exists ctr.
    exists cus.
    split; auto.
    split; auto.
    exists couts.
    split; auto.
    apply stmt_list_csem_outputs in H; auto.
Qed.
