(* Concrete Algebra Procedure Execution as a Function

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * Procedure Execution

    This library contains a straightforward definition of the
    semantics of procedure execution.  The semantics is specified
    using a function.  The semantics of statement execution is defined
    using a partial function that takes a runtime state and a list of
    statements and returns the final runtime environment and a list of
    terms that make up the procedure's outputs.  A runtime environment
    is a map from program variables to terms.  A runtime state contains

    - the current runtime environment,

    - the current trace, and

    - a list of the uniques that occur at the transmissions in the
      current trace. *)

Require Import FunInd Nat Bool Preamble Monad Proc Alg CSem.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** A runtime state *)

Record crun_state: Set :=
  mkCRSt {
      crenv: cenv;
      crtr: list cevt;
      cruniqs: list calg;
      crs: list nat }.

(** The semantics of expressions *)

Definition crun_expr (rst: crun_state) (ex: expr):
  option (crun_state * calg) :=
  match ex with
  | Quot_ s => Some (rst, CTg s)
  | Hash_ v =>
    x <- lookup v (crenv rst);;
    Some (rst, CHs x)
  | Pair_ u v =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    Some (rst, CPr x y)
  | Encr_ u v =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    match crs rst with
    | [] => Some (rst, CEn 0 x y)
    | r :: rs =>
      Some (mkCRSt (crenv rst)
                   (crtr rst)
                   (cruniqs rst)
                   rs,
            CEn r x y)
    end
  | Frst_ v =>
    x <- lookup v (crenv rst);;
    match x with
    | CPr y z => Some (rst, y)
    | _ => None
    end
  | Scnd_ v =>
    x <- lookup v (crenv rst);;
    match x with
    | CPr y z => Some (rst, z)
    | _ => None
    end
  | Decr_ u v =>
    x <- lookup u (crenv rst);;
    match x with
    | CEn _ y z =>
      k <- lookup v (crenv rst);;
      if negb (chas_enc k) && calg_eqb k (cinv z) then
        Some (rst, y)
      else
        None
    | _ => None
    end
  | Recv_ v =>
    c <- lookup v (crenv rst);;
    match crtr rst with
    | CRv d x :: tr =>
      match c with
      | CCh n =>
        if n =? d then
          Some (mkCRSt (crenv rst) tr (cruniqs rst) (crs rst), x)
        else
          None
      | _ => None
      end
    | _ => None
    end
  | Frsh =>
    match cruniqs rst with
    | u :: us =>
      Some (mkCRSt (crenv rst) (crtr rst) us (crs rst), u)
    | _ => None
    end
  end.

Lemma crun_expr_env_extends:
  forall rst ex rst' val,
    crun_expr rst ex = Some (rst', val) ->
    crenv rst' = crenv rst.
Proof.
  intros.
  destruct ex; simpl in H; inv H; auto.
  - apply do_some in H1.
    destruct H1.
    destruct H.
    inv H0; auto.
  - apply do_some in H1.
    destruct H1.
    destruct H.
    apply do_some in H0.
    destruct H0.
    destruct H0.
    inv H1; auto.
  - destruct (lookup n (crenv rst)).
    + destruct (lookup n0 (crenv rst)).
      * destruct (crs rst); inv H1; auto.
      * inv H1.
    + inv H1.
  - destruct (lookup n (crenv rst)).
    + destruct c; inv H1; auto.
    + inv H1.
  - destruct (lookup n (crenv rst)).
    + destruct c; inv H1; auto.
    + inv H1.
  - destruct (lookup n (crenv rst)).
    + destruct c; inv H1; auto.
      destruct (lookup n0 (crenv rst)); inv H0; auto.
      destruct (negb (chas_enc c) && calg_eqb c (cinv c2)); inv H1; auto.
    + inv H1.
  - destruct (cruniqs rst); inv H1; auto.
  - destruct (lookup n (crenv rst)); inv H1; auto.
    destruct (crtr rst); inv H0; auto.
    destruct c0; inv H1; auto.
    destruct c; inv H0; auto.
    destruct (n1 =? n0); inv H1; auto.
Qed.

(** Check that the type of [x] is compatible with [t]. *)

Definition ctype_check (x: calg) (t: type): bool :=
  type_eqb t Mesg || type_eqb (ctype_of x) t.

(** The semantics of statements *)

Definition crun_stmt (rst: crun_state) (cmd: stmt): option crun_state :=
  match cmd with
  | Bind (v, t) exp =>
    sx <- crun_expr rst exp;;
    let (rst, x) := sx in
    if ctype_check x t then
      Some (mkCRSt
              ((v, x) :: crenv rst)
              (crtr rst)
              (cruniqs rst)
              (crs rst))
    else
      None
   | Send u v =>
     match crtr rst with
     | CSd d x :: tr =>
       c <- lookup u (crenv rst);;
       match c with
       | CCh n =>
         if n =? d then
           y <- lookup v (crenv rst);;
           if calg_eqb x y then
             Some (mkCRSt (crenv rst) tr (cruniqs rst) (crs rst))
           else
             None
         else
           None
       | _ => None
       end
     | _ => None
    end
  | Same u v =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    if negb (chas_enc x) && calg_eqb x y then
      Some rst
    else
      None
  | Ltkp u v w =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    z <- lookup w (crenv rst);;
    match y, z with
    | CNm b, CNm c =>
      if calg_eqb x (CSk (Lt b c)) then
        Some rst
      else
        None
    | _, _ => None
    end
  | Invp u v =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    if negb (chas_enc x) && calg_eqb x (cinv y) then
      Some rst
    else
      None
  | Namp u v =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    match x, y with
    | CAk k, CNm b =>
      if akey_eqb k (Pb b) then
        Some rst
      else
        None
    | CIk k, CNm b =>
      if akey_eqb k (Pb b) then
        Some rst
      else
        None
    | _, _ => None
    end
  | Nm2p u v w =>
    x <- lookup u (crenv rst);;
    y <- lookup v (crenv rst);;
    z <- lookup w (crenv rst);;
    match x, y, z with
    | CAk k, CTg s, CNm c =>
      if akey_eqb k (Pb2 s c) then
        Some rst
      else
        None
    | CIk k, CTg s, CNm c =>
      if akey_eqb k (Pb2 s c) then
        Some rst
      else
        None
    | _, _, _ => None
    end
  | Return _ => None
end.

Lemma crun_stmt_env_extends:
  forall rst stmt rst',
    crun_stmt rst stmt = Some rst' ->
    exists ev, crenv rst' = ev ++ crenv rst.
Proof.
  intros.
  destruct stmt; simpl in H.
  - inv H.
  - destruct d.
    alt_option_dec (crun_expr rst e) p G; rewrite G in H.
    + inv H.
    + expand_let_pairs.
      destruct p.
      apply crun_expr_env_extends in G.
      simpl in H.
      destruct (ctype_check c0 t); inv H; auto.
      exists [(n, c0)]; simpl.
      rewrite G.
      auto.
  - exists []; simpl.
    destruct (crtr rst).
    inv H.
    destruct c.
    + destruct (lookup n (crenv rst)).
      * destruct c0; try inv H.
        destruct (n2 =? n1).
        -- destruct (lookup n0 (crenv rst)).
           ++ destruct (calg_eqb c c0); inv H1; simpl; auto.
           ++ inv H1.
        -- inv H1.
      * inv H.
    + inv H.
  - exists []; simpl.
    destruct (lookup n (crenv rst)).
    + destruct (lookup n0 (crenv rst)).
      * destruct (negb (chas_enc c) && calg_eqb c c0); inv H; simpl; auto.
      * inv H.
    + inv H.
  - exists []; simpl.
    destruct (lookup n (crenv rst)); inv H; auto.
    destruct (lookup n0 (crenv rst)); inv H1; auto.
    destruct (lookup n1 (crenv rst)); inv H0; auto.
    destruct c0; inv H1; auto.
    destruct c1; inv H0; auto.
    destruct (calg_eqb c (CSk (Lt n2 n3))); inv H1; auto.
  - exists []; simpl.
    destruct (lookup n (crenv rst)); inv H; auto.
    destruct (lookup n0 (crenv rst)); inv H1; auto.
    destruct (negb (chas_enc c) && calg_eqb c (cinv c0)); inv H0; auto.
  - exists []; simpl.
    destruct (lookup n (crenv rst)); inv H; auto.
    destruct (lookup n0 (crenv rst)); inv H1; auto.
    destruct c; inv H0; auto.
    + destruct c0; inv H1; auto.
      destruct (akey_eqb a (Pb n1)); inv H0; auto.
    + destruct c0; inv H1; auto.
      destruct (akey_eqb a (Pb n1)); inv H0; auto.
  - exists []; simpl.
    destruct (lookup n (crenv rst)); inv H; auto.
    destruct (lookup n0 (crenv rst)); inv H1; auto.
    destruct (lookup n1 (crenv rst)); inv H0; auto.
    destruct c; inv H1; auto.
    + destruct c0; inv H0; auto.
      destruct c1; inv H1; auto.
      destruct (akey_eqb a (Pb2 s n2)); inv H0; auto.
    + destruct c0; inv H0; auto.
      destruct c1; inv H1; auto.
      destruct (akey_eqb a (Pb2 s n2)); inv H0; auto.
Qed.

(** The semantics of lists of statements *)

Fixpoint crun_stmts (rst: crun_state) (stmts: list stmt):
  option (cenv * list calg) :=
  match stmts with
  | [] => None
  | [Return vs] =>
    match crtr rst, cruniqs rst with
    | [], [] =>
      xs <- map_m (fun x => lookup x (crenv rst)) vs;;
      Some (crenv rst, xs)
    | _, _ => None
    end
  | cmd :: stmts =>
    rst <- crun_stmt rst cmd;;
    crun_stmts rst stmts
  end.

Lemma crun_stmts_env_extends:
  forall rst stmts ev outs,
    crun_stmts rst stmts = Some (ev, outs) ->
    exists ev', ev = ev' ++ crenv rst.
Proof.
  intros rst stmts.
  revert rst.
  induction stmts; intros.
  - simpl in H.
    inv H.
  - destruct a; unfold crun_stmts in H; fold crun_stmts in H.
    + exists []; simpl.
      destruct stmts; inv H; auto.
      destruct (crtr rst); inv H1; auto.
      destruct (cruniqs rst); inv H0; auto.
      destruct (map_m (fun x : nat => lookup x (crenv rst)) l); inv H1; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply crun_stmt_env_extends in H.
      apply IHstmts in H0.
      repeat destruct_ex_and; subst.
      rewrite H.
      exists (x0 ++ x1).
      rewrite app_assoc; auto.
Qed.

(** Bind inputs with procedure parameters. *)

Fixpoint cbind_inputs (ds: list decl) (xs: list calg) (renv: cenv):
  option cenv :=
  match ds, xs with
  | [], [] => Some renv
  | (v, t) :: ds, x :: xs =>
    if ctype_check x t then
      cbind_inputs ds xs ((v, x) :: renv)
    else
      None
  | _, _ => None
  end.

(** The semantics of a procedure *)

Definition crun (p: proc) (inputs: list calg) (tr: list cevt)
           (us: list calg) (rs: list nat):
  option (cenv * list calg) :=
  renv <- cbind_inputs (ins p) inputs [];;
  crun_stmts (mkCRSt (rev renv) tr us rs) (body p).
