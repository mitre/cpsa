(* Concrete Execution Semantics

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * Concrete Execution Semantics

    This library presents a message algebra, called the concrete
    message algebra, that is very similar to the algebra used by the
    abstract execution semantics.  The only difference is the way in
    which it models encryption.  The signature used by the previous
    algebra has a binary operator for encryption [En], which suggests
    that two encryptions are the same if the plaintext and the key
    used to construct them are the same.  This is not true for
    implementations of encryption in actual use.  Instead, some
    randomness is added to an encryption during its construction in
    such a way that knowledge of the randomness is not needed to
    recover the plaintext by someone in possession of the decryption
    key.

    Probabilistic encryption is modeled by adding a random natural
    number to the construction of every term that represents an
    encryption.  A semantics is defined around the new algebra.  The
    new semantics is shown to be faithful to the abstract execution
    semantics, that is, for every run of the concrete execution
    semantics, there is a corresponding run of the abstract semantics
    in Theorem [csem_sem_faithfulness].  The concrete semantics is
    shown to be adequate with respect to the abstract execution
    semantics, that is for every run of the abstract execution
    semantics and choice of random values, there is a run of the
    concrete execution semantics, in Theorem [sem_csem_adequacy].

    The proof of adequacy makes demands on both the abstract and
    concrete execution semantics.  The proof depends on the fact that
    the following terms may not contain an encryption,

    - the key used during a decryption,

    - the terms compared with a sameness check, and

    - the terms compared with an inverse key predicate check. *)

Require Import FunInd ListSet Bool Arith Program Lia.
Require Import Preamble Monad Proc Alg Sem.
Import List.ListNotations.
Open Scope list_scope.

(** ** Definition and Faithfulness

    The key theorem in this section is [csem_sem_faithfulness], which
    states that whenever there is a run in the concrete executions
    semantics, there is a corresponding run in the abstract execution
    semantics.

    Concrete message algebra *)

Inductive calg: Set :=
| CTx: var -> calg              (* Text *)
| CDt: var -> calg              (* Data *)
| CNm: var -> calg              (* Name *)
| CSk: skey -> calg             (* Symmetric key *)
| CAk: akey -> calg             (* Asymmetric key *)
| CIk: akey -> calg             (* Inverse asymmetric key *)
| CCh: var -> calg              (* Channel *)
| CMg: var -> calg              (* Message *)
| CTg: string -> calg           (* Tag *)
| CPr: calg -> calg -> calg     (* Pair *)
| CEn: nat -> calg -> calg -> calg (* Probabilistic encryption *)
| CHs: calg -> calg.            (* Hash *)

(* An uninformative comment added to make coqdoc happy *)

(** Notice that encryptions take one more argument as compared with
    encryptions in the abstract message algebra.  The extra argument
    is some randomness.  See [CEn].  This is how probabilistic
    encryption is modeled. *)

Definition calg_dec:
  forall x y: calg, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality;
    try apply string_dec;
    decide equality.
Defined.
#[global]
Hint Resolve calg_dec : core.

Definition calg_eqb x y: bool :=
  if calg_dec x y then
    true
  else
    false.

Lemma calg_eq_correct:
  forall x y,
    calg_eqb x y = true <-> x = y.
Proof.
  intros.
  unfold calg_eqb.
  destruct (calg_dec x y); subst; intuition auto with *.
Qed.

Lemma calg_eq_complete:
  forall x y,
    calg_eqb x y = false <-> x <> y.
Proof.
  intros.
  unfold calg_eqb.
  destruct (calg_dec x y); subst; intuition auto with *.
Qed.

(** ** Type of an Algebra Term *)

Definition ctype_of (x: calg): type :=
  match x with
  | CTx _ => Text
  | CDt _ => Data
  | CNm _ => Name
  | CSk _ => Skey
  | CAk _ => Akey
  | CIk _ => Ikey
  | CCh _ => Chan
  | _ => Mesg
  end.

(** Concrete event *)

Inductive cevt: Set :=
| CSd: var -> calg -> cevt      (* Send *)
| CRv: var -> calg -> cevt.     (* Recv *)

(* An uninformative comment added to make coqdoc happy *)

Definition cevt_dec:
  forall x y: cevt, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
#[global]
Hint Resolve cevt_dec : core.

(** Inverse of a concrete message *)

Definition cinv (x: calg): calg :=
  match x with
  | CAk k => CIk k
  | CIk k => CAk k
  | k => k
  end.

Lemma cinv_cinv:
  forall c,
    cinv (cinv c) = c.
Proof.
  intros.
  destruct c; simpl; auto.
Qed.

Fixpoint chas_enc (x: calg): bool :=
  match x with
  | CHs y => chas_enc y
  | CPr y z => chas_enc y || chas_enc z
  | CEn _ _ _ => true
  | _ => false
  end.

(** Convert an concrete message [x] into its equivalent message.  This
    is done by forgetting the randomness in each encryption. *)

Fixpoint to_alg (x: calg): alg :=
  match x with
  | CTx v => Tx v
  | CDt v => Dt v
  | CNm v => Nm v
  | CSk k => Sk k
  | CAk k => Ak k
  | CIk k => Ik k
  | CCh v => Ch v
  | CMg v => Mg v
  | CTg z => Tg z
  | CPr y z => Pr (to_alg y) (to_alg z)
  | CEn _ y z => En (to_alg y) (to_alg z)
  | CHs y => Hs (to_alg y)
  end.

Lemma inv_to_alg:
  forall x,
    inv (to_alg x) = to_alg (cinv x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Lemma no_enc_eq:
  forall x y,
    chas_enc x = false ->
    to_alg x = to_alg y ->
    x = y.
Proof.
  induction x; induction y; intros;
    simpl in H; simpl in H0; inv H0; auto.
  - rewrite orb_false_iff in H.
    destruct H.
    apply IHx1 in H2; auto.
    apply IHx2 in H3; auto; subst; auto.
  - inv H.
  - apply IHx in H2; subst; auto.
Qed.

Lemma has_enc_to_alg:
  forall x,
    chas_enc x = has_enc (to_alg x).
Proof.
  induction x; intros; simpl; auto.
  rewrite IHx1.
  rewrite IHx2.
  auto.
Qed.

(** Convert a concrete event *)

Definition to_evt (e: cevt): evt :=
  match e with
  | CSd v x => Sd v (to_alg x)
  | CRv v x => Rv v (to_alg x)
  end.

(** A concrete runtime environment *)

Definition cenv: Set := list (pvar * calg).

Definition to_maplet (m: var * calg): var * alg :=
  let (v, x) := m in (v, to_alg x).

(** Convert a concrete environment *)

Definition to_env (ev: cenv): env :=
  map to_maplet ev.

(** Check the type of an element in the concrete algebra. *)

Definition is_cskey (x: calg): Prop :=
  is_skey (to_alg x).
#[global]
Hint Unfold is_cskey : core.

Inductive ctype_check: type -> calg -> Prop :=
| CText_check: forall v,
    ctype_check Text (CTx v)
| CData_check: forall v,
    ctype_check Data (CDt v)
| CName_check: forall v,
    ctype_check Name (CNm v)
| CSkey_check: forall k,
    ctype_check Skey (CSk k)
| CAkey_check: forall k,
    ctype_check Akey (CAk k)
| CIkey_check: forall k,
    ctype_check Ikey (CIk k)
| CChan_check: forall v,
    ctype_check Chan (CCh v)
| CMesg_check: forall x,
    ctype_check Mesg x.
#[global]
 Hint Constructors ctype_check : core.

Lemma type_check_equiv:
  forall (s: type) (c: calg),
    ctype_check s c <-> type_check s (to_alg c).
Proof.
  split; intros; destruct c; simpl in *; inv H; simpl; auto;
    destruct c2; inv H3; auto.
Qed.

(** The semantics of an expression

<<
   Parmeters:
   cenv:      Input environment
   list cevt: Input trace
   list calg: Input list of uniques
   list nat:  Input list of random values
   expr:      Expression code fragment
   calg:      Value of the expression
   list cevt: Output trace
   list calg: Output list of uniques
   list nat:  Output list of random values
>>

*)

Inductive expr_csem: cenv -> list cevt -> list calg -> list nat ->
                     expr -> calg -> list cevt ->
                     list calg -> list nat -> Prop :=
| CExpr_quot: forall ev tr us rs x,
    expr_csem ev tr us rs (Quot_ x) (CTg x) tr us rs
| CExpr_hash: forall ev tr us rs x a,
    lookup x ev = Some a ->
    expr_csem ev tr us rs (Hash_ x) (CHs a) tr us rs
| CExpr_pair: forall ev tr us rs x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_csem ev tr us rs (Pair_ x y) (CPr a b) tr us rs
| CExpr_encr_prob: forall ev tr us rs x y r a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_csem ev tr us (r :: rs) (Encr_ x y) (CEn r a b) tr us rs
| CExpr_encr_zero: forall ev tr us x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_csem ev tr us [] (Encr_ x y) (CEn 0 a b) tr us []
| CExpr_frst: forall ev tr us rs x a b,
    lookup x ev = Some (CPr a b) ->
    expr_csem ev tr us rs (Frst_ x) a tr us rs
| CExpr_scnd: forall ev tr us rs x a b,
    lookup x ev = Some (CPr a b) ->
    expr_csem ev tr us rs (Scnd_ x) b tr us rs
| CExpr_decr: forall ev tr us rs x y r a b,
    lookup x ev = Some (CEn r a b) ->
    lookup y ev = Some (cinv b) ->
    chas_enc (cinv b) = false ->
    expr_csem ev tr us rs (Decr_ x y) a tr us rs
| CExpr_frsh: forall ev tr us rs a,
    expr_csem ev tr (a :: us) rs Frsh_ a tr us rs
| CExpr_recv: forall ev tr us rs a c d,
    lookup c ev = Some (CCh d) ->
    expr_csem ev (CRv d a :: tr) us rs (Recv_ c) a tr us rs.
#[global]
Hint Constructors expr_csem : core.

Lemma lookup_ev:
  forall x cev a,
    lookup x cev = Some a ->
    lookup x (to_env cev) = Some (to_alg a).
Proof.
  intros.
  induction cev; simpl in *; auto.
  inv H.
  destruct a0 as [v c]; simpl in *.
  destruct (v =? x).
  - inv H; auto.
  - intuition.
Qed.

Local Ltac lookup_and_type_check :=
  repeat match goal with
         | [ H: lookup _ _ = Some _ |- _ ] =>
           apply lookup_ev in H; simpl in H
         | [ H: ctype_check _ _ |- _ ] =>
           rewrite type_check_equiv in H
         end.

(** Main theorem about expressions *)

Theorem expr_csem_expr_sem:
  forall ev tr us rs exp val tr' us' rs',
    expr_csem ev tr us rs exp val tr' us' rs' ->
    expr_sem (to_env ev) (map to_evt tr) (map to_alg us) exp
             (to_alg val) (map to_evt tr') (map to_alg us').
Proof.
  intros.
  inv H; simpl; auto; lookup_and_type_check; eauto.
  rewrite <- inv_to_alg in H1.
  rewrite has_enc_to_alg in H2.
  rewrite <- inv_to_alg in H2.
  eauto.
Qed.

(** The semantics of a statement

<<
   Parmeters:
   cenv:      Input environment
   list cevt: Input trace
   list calg: Input list of uniques
   list nat:  Input list of random values
   stmts:     Statements
   cenv:      Output environment
   list cevt: Output trace
   list calg: Output list of uniques
   list nat:  Output list of random values
>>
*)

Inductive stmt_csem: cenv -> list cevt -> list calg ->
                     list nat -> stmt -> cenv -> list cevt ->
                     list calg -> list nat -> Prop :=
| CStmt_bind: forall ev tr us rs exp val v s tr' us' rs',
    expr_csem ev tr us rs exp val tr' us' rs' ->
    ctype_check s val ->
    stmt_csem ev tr us rs (Bind (v, s) exp) ((v, val) :: ev) tr' us' rs'
| CStmt_send: forall ev tr us rs c d x a,
    lookup c ev = Some (CCh d) ->
    lookup x ev = Some a ->
    stmt_csem ev (CSd d a :: tr) us rs (Send c x) ev tr us rs
| CStmt_same: forall ev tr us rs x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    chas_enc a = false ->       (* For probabilistic encryption *)
    a = b ->                    (* Sameness check *)
    stmt_csem ev tr us rs (Same x y) ev tr us rs
| CStmt_invp: forall ev tr us rs x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    chas_enc a = false ->       (* For probabilistic encryption *)
    a = cinv b ->               (* Inverse check *)
    stmt_csem ev tr us rs (Invp x y) ev tr us rs.
#[global]
Hint Constructors stmt_csem : core.

Lemma stmt_csem_env_extends:
  forall ev tr us rs exp ev' tr' us' rs',
    stmt_csem ev tr us rs exp ev' tr' us' rs'->
    exists ev'', ev' = ev'' ++ ev.
Proof.
  intros.
  inv H.
  - exists [(v, val)]; auto.
  - exists []; auto.
  - exists []; auto.
  - exists []; auto.
Qed.

(** Main theorem about statements *)

Theorem stmt_csem_stmt_sem:
  forall ev tr us rs stmt ev' tr' us' rs',
    stmt_csem ev tr us rs stmt ev' tr' us' rs' ->
    stmt_sem (to_env ev) (map to_evt tr) (map to_alg us)
             stmt
             (to_env ev') (map to_evt tr') (map to_alg us').
Proof.
  intros; inv H; auto; lookup_and_type_check; eauto.
  - apply expr_csem_expr_sem in H0.
    apply Stmt_bind; auto.
  - apply Stmt_send; auto.
  - rewrite has_enc_to_alg in H2.
    eapply Stmt_same; eauto.
  - rewrite has_enc_to_alg in H2.
    eapply Stmt_invp; eauto.
    rewrite inv_to_alg; auto.
Qed.

(** The semantics of a statement list

    Parameters as for [stmt_csem] but with one extra argument, for
    outputs, and no output trace, list of uniques, and list of random
    values.

<<
   Parameters:
   cenv:      Input environment
   list cevt: Input trace
   list calg: Input list of uniques
   list nat:  Input list of random values
   list calg: Output list
   stmts:     Statements
   cenv:      Output environment
>>
 *)

Inductive stmt_list_csem:
  cenv -> list cevt -> list calg -> list nat ->
  list calg -> list stmt -> cenv -> Prop :=
| CStmt_return: forall ev rs outs vs,
    map_m (flip lookup ev) vs = Some outs ->
    stmt_list_csem ev [] [] rs outs [Return vs] ev
| CStmt_pair: forall ev tr us rs stmt ev' tr' us' rs'
                     outs stmts ev'',
    stmt_csem ev tr us rs stmt ev' tr' us' rs' ->
    stmt_list_csem ev' tr' us' rs' outs stmts ev'' ->
    stmt_list_csem ev tr us rs outs (stmt :: stmts) ev''.
#[global]
Hint Constructors stmt_list_csem : core.

Lemma stmt_list_csem_env_extends:
  forall ev tr us rs outs stmts ev',
    stmt_list_csem ev tr us rs outs stmts ev' ->
    exists ev'', ev' = ev'' ++ ev.
Proof.
  intros.
  induction H.
  exists []; auto.
  apply stmt_csem_env_extends in H.
  destruct H.
  destruct IHstmt_list_csem.
  subst.
  exists (x0 ++ x).
  apply app_assoc.
Qed.

Lemma lookup_none:
  forall x ev,
    lookup x ev = None <-> lookup x (to_env ev) = None.
Proof.
  split; intros; induction ev; simpl; auto;
    destruct a as [v y]; simpl in *; destruct (v =? x).
    + inv H.
    + intuition.
    + inv H.
    + intuition.
Qed.

Lemma map_m_lookup_cev:
  forall ev vs outs,
    map_m (flip lookup ev) vs = Some outs ->
    map_m (flip lookup (to_env ev)) vs = Some (map to_alg outs).
Proof.
  intros ev vs.
  revert ev.
  induction vs; intros; simpl; auto.
  - simpl in H; inv H; simpl; auto.
  - destruct outs as [|z zs].
    + apply map_m_nil in H; intuition.
    + apply map_m_pair in H.
      destruct H as [H G].
      unfold flip in H.
      unfold flip at 1.
      apply lookup_ev in H.
      rewrite H.
      apply IHvs in G.
      rewrite G.
      auto.
Qed.

(** Main theorem about statement lists *)

Theorem stmt_list_csem_stmt_list_sem:
  forall ev tr us rs outs stmts ev',
      stmt_list_csem ev tr us rs outs stmts ev' ->
      stmt_list_sem (to_env ev) (map to_evt tr) (map to_alg us)
                    (map to_alg outs) stmts (to_env ev').
Proof.
  intros.
  induction H; simpl; auto.
  - apply Stmt_return.
    apply map_m_lookup_cev; auto.
  - apply stmt_csem_stmt_sem in H; auto.
    eauto.
Qed.

(** Definitions and lemmas about inputs *)

Fixpoint mk_cenv (ds: list decl) (xs: list calg): cenv :=
  match (ds, xs) with
  | ((v, _) :: ds, x :: xs) =>
    (v, x) :: mk_cenv ds xs
  | _ => []
  end.

Lemma mk_cenv_env:
  forall ds cxs,
    to_env (mk_cenv ds cxs) = mk_env ds (map to_alg cxs).
Proof.
  induction ds; intros; simpl; auto.
  destruct a as [v s].
  destruct cxs as [|c cxs]; simpl; auto.
  rewrite IHds.
  auto.
Qed.

Inductive cins_inputs: list decl -> list calg -> Prop :=
| CIns_inputs_nil: cins_inputs nil nil
| CIns_inputs_pair: forall v s ds x xs,
    ctype_check s x ->
    cins_inputs ds xs ->
    cins_inputs ((v, s) :: ds) (x :: xs).
#[global]
Hint Constructors cins_inputs : core.

Lemma cins_ins_inputs:
  forall ds cxs,
    cins_inputs ds cxs -> ins_inputs ds (map to_alg cxs).
Proof.
  intros; induction H; simpl; auto.
  apply type_check_equiv in H; auto.
Qed.

(** Definition of the concrete semantics *)

Definition csem (p: proc) (rs: list nat) (cev: cenv) (e: role): Prop :=
  exists cins,
    inputs e = map to_alg cins /\
    cins_inputs (ins p) cins /\
    exists ctr cus couts,
      let ev_in := mk_cenv (ins p) cins in
      stmt_list_csem ev_in ctr cus rs couts (body p) cev /\
      trace e = map to_evt ctr /\
      uniqs e = map to_alg cus /\
      outputs e = map to_alg couts.

(** Main theorem about the concrete semantics *)

Theorem csem_sem_faithfulness:
  forall p rs cev e,
    csem p rs cev e -> sem p (to_env cev) e.
Proof.
  intros.
  unfold csem in H.
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         | [ H: exists _, _ |- _ ] =>
           destruct H
         | [ H: cins_inputs (ins _) _ |- _ ] =>
             apply cins_ins_inputs in H
         end.
  apply stmt_list_csem_stmt_list_sem in H1.
  rewrite mk_cenv_env in H1.
  unfold sem.
  repeat match goal with
         | [ H: _ e = map _ _ |- _ ] =>
           rewrite H
         end.
  split; auto.
Qed.

(** ** Adequacy

    Theorem [sem_csem_adequacy] states that whenever there is a run of
    the abstract semantics, there is a run of the concrete semantics.
    The proof of this theorem is much more difficult than the proof of
    the faithfulness theorem.  For that theorem, it is easy to create
    a witness by simply eliminating randomness using the [to_alg]
    function.  This section defines some simulation relations that
    help find the correct witness. *)

Lemma ex_lookup:
  forall v ev a,
    lookup v (to_env ev) = Some a ->
    exists b, lookup v ev = Some b.
Proof.
  induction ev; intros; simpl in *; auto.
  - inv H.
  - unfold to_maplet in H.
    repeat expand_let_pairs; simpl in *.
    destruct (alt_bool_dec (fst a =? v)) as [G|G];
      rewrite G in *.
    + inv H.
      destruct a as [u c]; simpl.
      exists c; auto.
    + eapply IHev; eauto.
Qed.

(** This theorem states that whenever an abstract expression has a
    value, there is corresponding value in the concrete semantics.
    The proof of this theorem depends on the fact that the key in a
    decryption must not contain an encryption, and therefore, no
    randomness.  See [CExpr_decr]. *)

Theorem expr_sem_expr_csem:
  forall ev tr us rs exp val tr' us' cev ctr cus,
    expr_sem ev tr us exp val tr' us' ->
    to_env cev = ev ->
    map to_evt ctr = tr ->
    map to_alg cus = us ->
    exists cval ctr' cus' rs',
      expr_csem cev ctr cus rs exp cval ctr' cus' rs' /\
      to_alg cval = val /\
      map to_evt ctr' = tr' /\
      map to_alg cus' = us'.
Proof.
  intros.
  destruct exp; inv H.
  - exists (CTg s).
    exists ctr.
    exists cus.
    exists rs.
    simpl.
    auto.
  - pose proof H7 as G.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in G; eauto.
    inv G; subst.
    exists (CHs x).
    repeat eexists.
    apply CExpr_hash; auto.
  - pose proof H8 as H.
    apply ex_lookup in H8.
    destruct H8.
    erewrite lookup_ev in H; eauto.
    inv H; subst.
    pose proof H12 as H.
    apply ex_lookup in H12.
    destruct H12.
    erewrite lookup_ev in H; eauto.
    inv H; subst.
    exists (CPr x x0); simpl.
    repeat eexists; eauto.
  - pose proof H8 as H.
    apply ex_lookup in H8.
    destruct H8.
    erewrite lookup_ev in H; eauto.
    inv H; subst.
    pose proof H12 as H.
    apply ex_lookup in H12.
    destruct H12.
    erewrite lookup_ev in H; eauto.
    inv H; subst.
    destruct rs as [|r rs].
    + exists (CEn 0 x x0); simpl.
      repeat eexists; eauto.
    + exists (CEn r x x0); simpl.
      repeat eexists; eauto.
  - pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists x1.
    repeat eexists; eauto.
  - pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists x2.
    repeat eexists; eauto.
  - pose proof H5 as H.
    apply ex_lookup in H5.
    destruct H5.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    rewrite inv_to_alg in H13.
    rewrite inv_to_alg in H9.
    pose proof H9 as H.
    apply ex_lookup in H9.
    destruct H9.
    erewrite lookup_ev in H; eauto.
    inv H.
    exists x1.
    repeat eexists; eauto.
    rewrite <- has_enc_to_alg in H13.
    eapply CExpr_decr; eauto.
    rewrite H1.
    apply eq_sym in H3.
    apply no_enc_eq in H3; subst; auto.
  - destruct cus as [| u cus]; simpl in H5; inv H5.
    exists u.
    repeat eexists; eauto.
  - destruct ctr as [| e ctr]; simpl in H5; inv H5.
    destruct e; simpl in H0; inv H0.
    pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists c.
    repeat eexists; eauto.
Qed.

(** The [stmt_send] conditions ensures that a transmitted message
    agrees with what is in the environment. *)

Definition stmt_send (ev: cenv) (ctr: list cevt) (s: stmt): Prop :=
  match s, ctr with
  | Send c x, CSd d a :: _ =>
    lookup x ev = Some a
  | _, _ => True
  end.

(** This theorem states that whenever an abstract state transitions,
    there is corresponding transition in the concrete semantics.  The
    proof of this theorem depends on the fact that the sameness and
    inverse predicate checks never succeed when given a term that
    contains an encryption, so checked terms contain no randomness.
    See [CStmt_same] and [CStmt_invp]. *)

Theorem stmt_sem_stmt_csem:
  forall ev tr us cev ctr cus rs stmt ev' tr' us',
    stmt_sem ev tr us stmt ev' tr' us' ->
    to_env cev = ev ->
    map to_evt ctr = tr ->
    map to_alg cus = us ->
    stmt_send cev ctr stmt ->
    exists cev' ctr' cus' rs',
      stmt_csem cev ctr cus rs stmt cev' ctr' cus' rs' /\
      to_env cev' = ev' /\
      map to_evt ctr' = tr' /\
      map to_alg cus' = us'.
Proof.
  intros.
  destruct stmt; inv H.
  - apply expr_sem_expr_csem
      with (rs := rs)
           (cev := cev)
           (ctr := ctr)
           (cus := cus)
      in H9; auto.
    repeat destruct_ex_and; subst.
    rewrite <- type_check_equiv in H13.
    exists ((v, x) :: cev).
    exists x0.
    exists x1.
    exists x2.
    auto.
  - destruct ctr as [|e ctr].
    simpl in H7.
    inv H7.
    destruct e; simpl in H7; inv H7.
    pose proof H9 as H.
    apply ex_lookup in H9.
    destruct H9.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    pose proof H13 as H.
    apply ex_lookup in H13.
    destruct H13.
    erewrite lookup_ev in H; eauto.
    inv H.
    unfold stmt_send in H3.
    rewrite H1 in H3.
    inv H3.
    repeat eexists; eauto.
  - exists cev.
    exists ctr.
    exists cus.
    exists rs.
    pose proof H6 as H.
    apply ex_lookup in H6.
    destruct H6.
    erewrite lookup_ev in H; eauto.
    inv H.
    pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    rewrite <- has_enc_to_alg in H11; auto.
    apply eq_sym in H4.
    apply no_enc_eq in H4; auto; subst.
    split; auto.
    eapply CStmt_same; eauto.
  - exists cev.
    exists ctr.
    exists cus.
    exists rs.
    pose proof H6 as H.
    apply ex_lookup in H6.
    destruct H6.
    erewrite lookup_ev in H; eauto.
    inv H.
    pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    rewrite inv_to_alg in H11.
    rewrite <- has_enc_to_alg in H11; auto.
    rewrite inv_to_alg in H2.
    apply eq_sym in H2.
    apply no_enc_eq in H2; auto; subst.
    split; auto.
    eapply CStmt_invp; eauto.
Qed.

(** So far, the proofs have been fairly straightforward.  But that
    is all about to change.  The next step is to show that whenever
    there are sequences of abstract state transitions, there are
    corresponding sequences of transitions in the concrete semantics.
    In the previous theorem, the transmitted term had to agree with
    what was in the environment.  The challenge is to find a trace
    that serves as a witness that has that property.

    There is considerable freedom in the choice of received terms in
    the trace of our witness.  The primary requirement is that when
    randomness is removed, they agree with received terms in the
    abstract trace.  Therefore, we choose received terms that have
    zero as the randomness for any encryption within the term.

    We also have to find a sequence of concrete fresh values that
    corresponds to a sequence of abstract fresh values.  This is easy,
    because fresh values are basic values and contain no encryptions
    and so no randomness. *)

(** Create a concrete term from an abstract term without randomness *)

Fixpoint to_calg (x: alg): calg :=
  match x with
  | Tx v => CTx v
  | Dt v => CDt v
  | Nm v => CNm v
  | Sk k => CSk k
  | Ak k => CAk k
  | Ik k => CIk k
  | Ch v => CCh v
  | Mg v => CMg v
  | Tg z => CTg z
  | Pr y z => CPr (to_calg y) (to_calg z)
  | En y z => CEn 0 (to_calg y) (to_calg z)
  | Hs y => CHs (to_calg y)
  end.

Lemma to_alg_calg:
  forall val,
    to_alg (to_calg val) = val.
Proof.
  induction val; simpl; auto.
  - rewrite IHval1.
    rewrite IHval2.
    auto.
  - rewrite IHval1.
    rewrite IHval2.
    auto.
  - rewrite IHval.
    auto.
Qed.

Lemma map_to_alg_calg:
  forall xs,
    map to_alg (map to_calg xs) = xs.
Proof.
  induction xs; simpl; auto.
  rewrite to_alg_calg.
  rewrite IHxs; auto.
Qed.

(** Concrete terms without encryptions have no randomness. *)

Lemma to_calg_alg:
  forall val,
    chas_enc val = false ->
    to_calg (to_alg val) = val.
Proof.
  induction val; intros; simpl in *; auto.
  - rewrite orb_false_iff in H.
    destruct H.
    rewrite IHval1; auto.
    rewrite IHval2; auto.
  - inv H.
  - rewrite IHval; auto.
Qed.

Lemma has_enc_lookup:
  forall x cev v,
    has_enc x = false ->
    lookup v (to_env cev) = Some x ->
    lookup v cev = Some (to_calg x).
Proof.
  intros.
  pose proof H0 as G.
  apply ex_lookup in H0.
  destruct H0 as [y].
  pose proof H0 as F.
  apply lookup_ev in H0.
  rewrite G in H0.
  inv H0.
  rewrite <- has_enc_to_alg in H.
  rewrite to_calg_alg; auto.
Qed.

Definition to_cmaplet (m: var * alg): var * calg :=
  let (v, x) := m in (v, to_calg x).

(** Convert a concrete environment.  This is used to convert inputs to
    a role.  Since they are basic values, they do not contain
    randomness. *)

Definition to_cenv (ev: env): cenv :=
  map to_cmaplet ev.

Lemma to_env_cenv:
  forall ev,
    to_env (to_cenv ev) = ev.
Proof.
  induction ev; simpl; auto.
  rewrite IHev.
  unfold to_cmaplet.
  unfold to_maplet.
  repeat expand_let_pairs; simpl.
  rewrite to_alg_calg; auto.
Qed.

Lemma mk_env_cenv:
  forall ds xs,
    to_cenv (mk_env ds xs) = mk_cenv ds (map to_calg xs).
Proof.
  induction ds; intros; simpl; auto.
  destruct a as [v s].
  destruct xs as [|c xxs]; simpl; auto.
  rewrite IHds.
  auto.
Qed.

Lemma map_m_lookup_ev:
  forall ev vs outs,
    map_m (flip lookup (to_env ev)) vs = Some outs ->
    exists couts,
      map_m (flip lookup ev) vs = Some couts /\
      map to_alg couts = outs.
Proof.
  intros ev vs.
  revert ev.
  induction vs; intros; simpl in *; auto.
  - inv H.
    exists []; simpl; auto.
  - apply do_some in H.
    destruct H as [x].
    destruct H.
    apply do_some in H0.
    destruct H0 as [xs].
    destruct H0.
    inv H1.
    apply IHvs in H0.
    destruct H0 as [couts'].
    destruct H0; subst.
    pose proof H as G.
    apply ex_lookup in H.
    destruct H as [b].
    exists (b :: couts').
    unfold flip at 1.
    rewrite H.
    rewrite H0.
    split; auto.
    simpl.
    unfold flip in G.
    apply lookup_ev in H.
    rewrite H in G.
    inv G; subst; auto.
Qed.

(** Relate expressions

<<
   Parmeters:
   cenv:      Input environment
   list evt:  Input trace
   list alg:  Input list of uniques
   list nat:  Input list of random values
   expr:      Expression code fragment
   calg:      Value of the expression
   list evt:  Output trace
   list alg:  Output list of uniques
   list nat:  Output list of random values
   list cevt: Output added concrete events
   list calg: Output added concrete uniques
>>
*)

Inductive expr_sim:
  cenv -> list evt -> list alg -> list nat -> expr ->
  calg -> list evt -> list alg -> list nat ->
  list cevt -> list calg -> Prop :=
| Sim_quot: forall ev tr us rs x,
    expr_sim ev tr us rs (Quot_ x) (CTg x)
             tr us rs [] []
| Sim_hash: forall ev tr us rs x a,
    lookup x ev = Some a ->
    expr_sim ev tr us rs (Hash_ x) (CHs a) tr us rs [] []
| Sim_pair: forall ev tr us rs x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_sim ev tr us rs (Pair_ x y) (CPr a b) tr us rs [] []
| Sim_encr_prob: forall ev tr us rs x y r a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_sim ev tr us (r :: rs) (Encr_ x y) (CEn r a b) tr us rs [] []
| Sim_encr_zero: forall ev tr us x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    expr_sim ev tr us [] (Encr_ x y) (CEn 0 a b) tr us [] [] []
| Sim_frst: forall ev tr us rs x a b,
    lookup x ev = Some (CPr a b) ->
    expr_sim ev tr us rs (Frst_ x) a tr us rs [] []
| Sim_scnd: forall ev tr us rs x a b,
    lookup x ev = Some (CPr a b) ->
    expr_sim ev tr us rs (Scnd_ x) b tr us rs [] []
| Sim_decr: forall ev tr us rs x y r a b,
    lookup x ev = Some (CEn r a b) ->
    lookup y ev = Some (cinv b) ->
    chas_enc (cinv b) = false ->
    expr_sim ev tr us rs (Decr_ x y) a tr us rs [] []
| Sim_frsh: forall ev tr us rs a,
    expr_sim ev tr (a :: us) rs Frsh_ (to_calg a) tr us rs [] [to_calg a]
| Sim_recv: forall ev tr us rs a c d,
    lookup c ev = Some (CCh d) ->
    expr_sim ev (Rv d a :: tr) us rs (Recv_ c) (to_calg a)
             tr us rs [CRv d (to_calg a)] [].
#[global]
Hint Constructors expr_sim : core.

Lemma expr_sim_to_alg:
  forall cev tr us rs exp val tr' us' rs' dtr dus,
    expr_sim cev tr us rs exp val tr' us' rs' dtr dus ->
    map to_evt dtr ++ tr' = tr /\ map to_alg dus ++ us' = us.
Proof.
  intros.
  destruct exp; inv H; simpl; auto;
    rewrite to_alg_calg; auto.
Qed.

(** The simulation always exists *)

Lemma expr_sem_expr_sim:
  forall ev tr us exp val rs tr' us' cev,
    expr_sem ev tr us exp val tr' us' ->
    to_env cev = ev ->
    exists cval rs' dtr dus,
      expr_sim cev tr us rs exp cval tr' us' rs' dtr dus /\
      to_alg cval = val.
Proof.
  intros.
  destruct exp; inv H.
  - exists (CTg s); exists rs; exists []; exists [].
    auto.
  - pose proof H5 as H.
    apply ex_lookup in H5.
    destruct H5.
    erewrite lookup_ev in H; eauto.
    inv H.
    exists (CHs x); exists rs; exists []; exists [].
    auto.
  - pose proof H6 as H.
    apply ex_lookup in H6.
    destruct H6.
    erewrite lookup_ev in H; eauto.
    inv H.
    pose proof H10 as H.
    apply ex_lookup in H10.
    destruct H10.
    erewrite lookup_ev in H; eauto.
    inv H.
    exists (CPr x x0); exists rs; exists []; exists [].
    auto.
  - pose proof H6 as H.
    apply ex_lookup in H6.
    destruct H6.
    erewrite lookup_ev in H; eauto.
    inv H.
    pose proof H10 as H.
    apply ex_lookup in H10.
    destruct H10.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct rs as [| r rs].
    + exists (CEn 0 x x0); exists []; exists []; exists [].
      auto.
    + exists (CEn r x x0); exists rs; exists []; exists [].
      auto.
  - pose proof H5 as H.
    apply ex_lookup in H5.
    destruct H5.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists x1; exists rs; exists []; exists [].
    split; auto.
    eapply Sim_frst; eauto.
  - pose proof H5 as H.
    apply ex_lookup in H5.
    destruct H5.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists x2; exists rs; exists []; exists [].
    split; auto.
    eapply Sim_scnd; eauto.
  - pose proof H3 as H.
    apply ex_lookup in H3.
    destruct H3.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    pose proof H7 as H.
    apply ex_lookup in H7.
    destruct H7.
    erewrite lookup_ev in H; eauto.
    inv H.
    rewrite inv_to_alg in *.
    apply eq_sym in H3.
    rewrite <- has_enc_to_alg in H11.
    apply no_enc_eq in H3; auto; subst.
    exists x1; exists rs; exists []; exists [].
    split; auto.
    eapply Sim_decr; eauto.
  - exists (to_calg val); exists rs; exists [];
      exists [to_calg val].
    rewrite to_alg_calg.
    auto.
  - pose proof H5 as H.
    apply ex_lookup in H5.
    destruct H5.
    erewrite lookup_ev in H; eauto.
    inv H.
    destruct x; simpl in H2; inv H2.
    exists (to_calg val); exists rs;
      exists [CRv d (to_calg val)]; exists [].
    rewrite to_alg_calg.
    auto.
Qed.

Lemma expr_sim_injective:
  forall cev tr us rs exp
         val' tr' us' rs' dtr' cus'
         val'' tr'' us'' rs'' dtr'' cus'',
    expr_sim cev tr us rs exp val' tr' us' rs' dtr' cus' ->
    expr_sim cev tr us rs exp val'' tr'' us'' rs'' dtr'' cus'' ->
    val' = val'' /\ tr' = tr'' /\ us' = us'' /\
    rs' = rs'' /\ dtr' = dtr'' /\ cus' = cus''.
Proof.
  intros.
  destruct exp; inv H; inv H0; intuition.
  - rewrite H5 in H6; inv H6; auto.
  - rewrite H7 in H6; inv H6.
    rewrite H15 in H14; inv H14; auto.
  - rewrite H7 in H15; inv H15.
    rewrite H16 in H14; inv H14; auto.
  - rewrite H7 in H5; inv H5.
    rewrite H6 in H14; inv H14; auto.
  - rewrite H6 in H5; inv H5; auto.
  - rewrite H6 in H5; inv H5; auto.
  - rewrite H3 in H2; inv H2; auto.
Qed.

(** The desired simulation between abstract and concrete expressions *)

Lemma expr_sem_sim_csem:
  forall ev tr us exp val tr' us'
         cev cval rs rs' dtr dus ctr cus,
    expr_sem ev tr us exp val tr' us' ->
    expr_sim cev tr us rs exp cval tr' us' rs' dtr dus ->
    to_env cev = ev ->
    to_alg cval = val ->
    expr_csem cev (dtr ++ ctr) (dus ++ cus) rs exp cval ctr cus rs'.
Proof.
  intros.
  pose proof H0 as G.
  apply expr_sim_to_alg in H0.
  destruct H0.
  destruct exp; inv H; inv G; simpl; auto.
  - eapply CExpr_frst; eauto.
  - eapply CExpr_scnd; eauto.
  - eapply CExpr_decr; eauto.
Qed.

(** Relate statements

<<
   Parmeters:
   cenv:      Input environment
   list evt:  Input trace
   list alg:  Input list of uniques
   list nat:  Input list of random values
   stmt:      Statement
   cenv:      Output environment
   list evt:  Output trace
   list alg:  Ouput list of uniques
   list nat:  Output list of random values
   list cevt: Output added concrete events
   list calg: Output added concrete uniques
>>
*)

Inductive stmt_sim:
  cenv -> list evt -> list alg -> list nat -> stmt ->
  cenv -> list evt -> list alg -> list nat ->
  list cevt -> list calg -> Prop :=
| Sim_bind: forall ev tr us rs v s exp val
                   tr' us' rs' dtr dus,
    expr_sim ev tr us rs exp val tr' us' rs' dtr dus ->
    ctype_check s val ->
    stmt_sim ev tr us rs (Bind (v, s) exp)
             ((v, val) :: ev) tr' us' rs' dtr dus
| Sim_send: forall ev tr us rs c x d a,
    lookup c ev = Some (CCh d) ->
    lookup x ev = Some a ->
    stmt_sim ev (Sd d (to_alg a) :: tr) us rs
             (Send c x) ev tr us rs [CSd d a] []
| Sim_same: forall ev tr us rs x y,
    stmt_sim ev tr us rs (Same x y) ev tr us rs [] []
| Sim_invp: forall ev tr us rs x y,
    stmt_sim ev tr us rs (Invp x y) ev tr us rs [] [].
#[global]
Hint Constructors stmt_sim : core.

Lemma stmt_sim_to_alg:
  forall ev tr us rs stmt ev' tr' us' rs' dtr dus,
    stmt_sim ev tr us rs stmt ev' tr' us' rs' dtr dus ->
    map to_evt dtr ++ tr' = tr /\ map to_alg dus ++ us' = us.
Proof.
  intros.
  destruct stmt; inv H; simpl; auto.
  apply expr_sim_to_alg in H6; auto.
Qed.

(** The simulation always exists *)

Lemma stmt_sem_stmt_sim:
  forall cev ev tr us rs stmt ev' tr' us',
    stmt_sem ev tr us stmt ev' tr' us' ->
    to_env cev = ev ->
    exists cev' rs' dtr dus,
      stmt_sim cev tr us rs stmt cev' tr' us' rs' dtr dus /\
      to_env cev' = ev'.
Proof.
  intros.
  inv H.
  - apply expr_sem_expr_sim
      with (rs := rs)
           (cev := cev) in H1; auto.
    destruct H1 as [cval G].
    destruct G as [rs' G].
    destruct G as [dtr G].
    destruct G as [dus G].
    destruct G; subst.
    rewrite <- type_check_equiv in H2.
    exists ((v, cval) :: cev).
    exists rs'.
    exists dtr.
    exists dus.
    simpl.
    split; auto.
  - pose proof H2 as G.
    apply ex_lookup in H2.
    destruct H2 as [b].
    pose proof H1 as F.
    apply has_enc_lookup in H1; simpl; auto.
    simpl in H1.
    pose proof H as E.
    apply lookup_ev in H.
    rewrite H in G.
    inv G.
    exists cev.
    exists rs.
    exists [CSd d b].
    exists [].
    split; auto.
  - pose proof H1 as G.
    apply has_enc_lookup in H1; simpl; auto.
    pose proof H2 as F.
    apply has_enc_lookup in H2; simpl; auto.
    exists cev.
    exists rs.
    exists [].
    exists [].
    split; auto.
  - pose proof H1 as G.
    apply has_enc_lookup in H1; simpl; auto.
    rewrite inv_has_enc in H3.
    pose proof H2 as F.
    apply has_enc_lookup in H2; simpl; auto.
    exists cev.
    exists rs.
    exists [].
    exists [].
    split; auto.
Qed.

Lemma stmt_sim_injective:
  forall cev tr us rs stmt
         cev' tr' us' rs' dtr' dus'
         cev'' tr'' us'' rs'' dtr'' dus'',
    stmt_sim cev tr us rs stmt cev' tr' us' rs' dtr' dus' ->
    stmt_sim cev tr us rs stmt cev'' tr'' us'' rs'' dtr'' dus'' ->
    cev' = cev'' /\ tr' = tr'' /\ us' = us'' /\
    rs' = rs'' /\ dtr' = dtr'' /\ dus' = dus''.
Proof.
  intros.
  destruct stmt; inv H; inv H0; intuition.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - eapply expr_sim_injective in H7; eauto.
    repeat destruct_ex_and; subst; auto.
  - rewrite H14 in H17.
    inv H17; subst; auto.
Qed.

(** The desired simulation between abstract and concrete statements *)

Lemma stmt_sem_sim_csem:
  forall cev ev tr us rs stmt ev' tr' us'
         cev' rs' dtr dus ctr cus,
    stmt_sem ev tr us stmt ev' tr' us' ->
    stmt_sim cev tr us rs stmt cev' tr' us' rs' dtr dus ->
    to_env cev = ev ->
    to_env cev' = ev' ->
    stmt_csem cev (dtr ++ ctr) (dus ++ cus) rs stmt
              cev' ctr cus rs'.
Proof.
  intros.
  pose proof H0 as G.
  apply stmt_sim_to_alg in H0.
  destruct H0.
  destruct stmt; inv H; inv G; simpl in *; subst; auto.
  - inv H10.
    eapply expr_sem_sim_csem in H15; eauto.
  - apply has_enc_lookup in H6; auto.
    apply has_enc_lookup in H7; auto.
    eapply CStmt_same; eauto.
    rewrite has_enc_to_alg.
    rewrite to_alg_calg; auto.
  - apply has_enc_lookup in H6; auto.
    pose proof H11 as G.
    rewrite inv_has_enc in H11.
    apply has_enc_lookup in H7; auto.
    eapply CStmt_invp; eauto.
    rewrite has_enc_to_alg.
    rewrite to_alg_calg; auto.
    destruct b; auto.
Qed.

(** Relate sequences of statements

<<
   Parmeters:
   cenv:      Input environment
   list evt:  Input trace
   list alg:  Input list of uniques
   list nat:  Input list of random values
   list calg: Output list
   list stmt: Statements
   cenv:      Output environment
   list cevt: Output added concrete events
   list calg: Output added concrete uniques
>>
*)
Inductive stmt_list_sim:
  cenv -> list evt -> list alg -> list nat -> list calg -> list stmt ->
  cenv -> list cevt -> list calg -> Prop :=
| Sim_return: forall ev rs outs vs,
    map_m (flip lookup ev) vs = Some outs ->
    stmt_list_sim ev [] [] rs outs [Return vs] ev [] []
| Sim_stmts: forall ev tr us rs outs s stmts ev' tr' us' rs' dtr dus
                    ev'' ctr cus,
    stmt_sim ev tr us rs s ev' tr' us' rs' dtr dus ->
    stmt_list_sim ev' tr' us' rs' outs stmts ev'' ctr cus ->
    stmt_list_sim ev tr us rs outs (s :: stmts)
                  ev'' (dtr ++ ctr) (dus ++ cus).
#[global]
Hint Constructors stmt_list_sim : core.

Lemma stmt_list_sim_to_alg:
  forall stmts cev tr us rs couts cev' ctr cus,
    stmt_list_sim cev tr us rs couts stmts cev' ctr cus ->
    map to_evt ctr = tr /\ map to_alg cus = us.
Proof.
  induction stmts; intros; inv H; simpl; auto.
  apply stmt_sim_to_alg in H7; auto.
  destruct H7; subst.
  apply IHstmts in H11.
  destruct H11; subst.
  repeat rewrite map_app; auto.
Qed.

(** The simulation always exists *)

Lemma stmt_list_sem_stmt_list_sim:
  forall stmts ev tr us rs outs ev' cev,
    stmt_list_sem ev tr us outs stmts ev' ->
    to_env cev = ev ->
    exists couts cev' ctr cus,
      stmt_list_sim cev tr us rs couts stmts cev' ctr cus /\
      map to_alg couts = outs.
Proof.
  induction stmts; intros; simpl; auto; inv H.
  - apply map_m_lookup_ev in H8.
    destruct H8 as [couts].
    destruct H; subst.
    exists couts.
    exists cev.
    exists [].
    exists [].
    auto.
  - pose proof H7 as H.
    apply stmt_sem_stmt_sim
      with (cev := cev) (rs := rs) in H7; auto.
    destruct H7 as [cev' G].
    destruct G as [rs' G].
    destruct G as [dtr G].
    destruct G as [dus G].
    destruct G; subst.
    pose proof H0 as F.
    apply stmt_sim_to_alg in H0.
    destruct H0; subst.
    apply IHstmts
      with (rs := rs') (cev := cev') in H9; auto.
    destruct H9 as [couts G].
    destruct G as [cev'' G].
    destruct G as [ctr G].
    destruct G as [cus G].
    exists couts.
    exists cev''.
    exists (dtr ++ ctr).
    exists (dus ++ cus).
    destruct G; subst.
    split; auto.
    pose proof H0 as G.
    apply stmt_list_sim_to_alg in H0.
    destruct H0; subst.
    eapply Sim_stmts in G; eauto.
Qed.

(** The desired simulation between abstract and concrete statement
    sequences *)

Lemma stmt_list_sem_sim_csem:
  forall stmts ev tr us outs ev' cev rs
         couts cev' ctr cus,
    stmt_list_sem ev tr us outs stmts ev' ->
    stmt_list_sim cev tr us rs couts stmts
                  cev' ctr cus ->
    to_env cev = ev ->
    map to_evt ctr = tr ->
    map to_alg cus = us ->
    stmt_list_csem cev ctr cus rs
                   couts stmts cev'.
Proof.
  induction stmts; intros; inv H; inv H0; simpl; auto.
  - inv H9.
  - pose proof H7 as G.
    apply stmt_sim_to_alg in H7.
    repeat rewrite map_app in H7.
    destruct H7.
    rewrite app_inv_head_iff in H; subst.
    rewrite app_inv_head_iff in H0; subst.
    pose proof H10 as F.
    apply stmt_sem_stmt_sim
      with (cev := cev) (rs := rs) in H10; auto.
    destruct H10 as [cev'' D].
    destruct D as [rs'' D].
    destruct D as [dtr' D].
    destruct D as [dus' D].
    destruct D as [D]; subst.
    eapply stmt_sim_injective in D; eauto.
    repeat destruct_ex_and; subst.
    eapply stmt_sem_sim_csem in G; eauto.
Qed.

Theorem stmt_list_sem_stmt_list_csem:
  forall ev tr us outs stmts ev' cev rs,
    stmt_list_sem ev tr us outs stmts ev' ->
    to_env cev = ev ->
    exists ctr cus couts cev',
      stmt_list_csem cev ctr cus rs couts stmts cev' /\
      map to_evt ctr = tr /\
      map to_alg cus = us /\
      map to_alg couts = outs.
Proof.
  intros.
  pose proof H as G.
  apply stmt_list_sem_stmt_list_sim
    with (rs := rs) (cev := cev) in H; auto.
  destruct H as [couts'].
  destruct H as [cev'].
  destruct H as [ctr'].
  destruct H as [cus'].
  destruct H.
  exists ctr'.
  exists cus'.
  exists couts'.
  exists cev'.
  pose proof H as F.
  apply stmt_list_sim_to_alg in F; auto.
  destruct F.
  eapply stmt_list_sem_sim_csem in H; eauto.
Qed.

Lemma ins_cins_inputs:
  forall ds xs,
    ins_inputs ds xs -> cins_inputs ds (map to_calg xs).
Proof.
  intros; induction H; simpl; auto.
  apply CIns_inputs_pair; auto.
  apply type_check_equiv.
  rewrite to_alg_calg; auto.
Qed.

Theorem sem_csem_adequacy:
  forall p ev rs e,
    sem p ev e ->
    exists cev,
      csem p rs cev e.
Proof.
  intros.
  unfold sem in H.
  destruct H as [H G].
  apply ins_cins_inputs in H.
  apply stmt_list_sem_stmt_list_csem
    with (cev := to_cenv (mk_env (ins p) (inputs e)))
         (rs := rs) in G; auto.
  - destruct G as [ctr G].
    destruct G as [cus G].
    destruct G as [couts G].
    destruct G as [cev' G].
    destruct G as [G F].
    rewrite mk_env_cenv in G.
    exists cev'.
    unfold csem.
    exists (map to_calg (inputs e)).
    rewrite map_to_alg_calg.
    split; auto.
    split; auto.
    exists ctr.
    exists cus.
    exists couts.
    split; auto.
    intuition.
  - rewrite to_env_cenv; auto.
Qed.

(** ** Alternate Concrete Execution Semantics

    In this semantics, the inputs are computed from the given output
    environment instead of being assumed to exist, and outputs are
    computed from the environment and the statement list. *)

Definition mk_ins (ev: cenv) (ds: list decl): list calg :=
  map snd (skipn (length ev - length ds) ev).

Fixpoint mk_outs (ev: cenv) (stmts: list stmt): option (list calg) :=
  match stmts with
  | [] => None
  | [Return vs] => map_m (flip lookup ev) vs
  | _ :: stmts => mk_outs ev stmts
  end.

Definition csem' (p: proc) (rs: list nat) (cev: cenv) (e: role): Prop :=
  let cins := mk_ins cev (ins p) in
  inputs e = map to_alg cins /\
  cins_inputs (ins p) cins /\
  exists ctr cus,
    trace e = map to_evt ctr /\
    uniqs e = map to_alg cus /\
    let ev_in := mk_cenv (ins p) cins in
    exists couts,
      mk_outs cev (body p) = Some couts /\
      stmt_list_csem ev_in ctr cus rs couts (body p) cev /\
      outputs e = map to_alg couts.

Theorem csem'_csem:
  forall p rs cev ex,
    csem' p rs cev ex ->
    csem p rs cev ex.
Proof.
  intros.
  unfold csem' in H.
  repeat destruct_ex_and.
  unfold csem.
  eexists; intuition; eauto.
    eexists; eexists; eexists;
      intuition; eauto.
Qed.

Functional Scheme mk_cenv_ind :=
  Induction for mk_cenv Sort Prop.

Lemma ins_inputs_length:
  forall inputs ds,
    cins_inputs ds inputs ->
    length (mk_cenv ds inputs) = length ds.
Proof.
  intros.
  functional induction (mk_cenv ds inputs); auto.
  - inv H.
  - inv H; simpl.
    apply IHc in H6.
    rewrite H6; auto.
Qed.

Lemma mk_ins_inputs:
  forall inputs ds ev,
    cins_inputs ds inputs ->
    mk_ins (ev ++ mk_cenv ds inputs) ds = inputs.
Proof.
  intros.
  unfold mk_ins.
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
  rewrite Nat.sub_diag; simpl.
  clear G.
  induction H; simpl; auto.
  rewrite IHcins_inputs; auto.
Qed.

Functional Scheme mk_outs_ind :=
  Induction for mk_outs Sort Prop.

Lemma stmt_list_csem_outputs:
  forall ev tr us rs outs stmts ev',
    stmt_list_csem ev tr us rs outs stmts ev' ->
    mk_outs ev' stmts = Some outs.
Proof.
  intros.
  revert H.
  revert ev.
  revert tr.
  revert us.
  revert rs.
  functional induction (mk_outs ev' stmts); intros.
  - inv H.
  - inv H; auto.
    inv H7.
  - inv H.
    inv H7.
  - inv H.
    apply IHo in H9; auto.
  - inv H.
    apply IHo in H9; auto.
  - inv H.
    apply IHo in H9; auto.
  - inv H.
    apply IHo in H9; auto.
Qed.

Theorem csem_csem':
  forall p rs cev ex,
    csem p rs cev ex ->
    csem' p rs cev ex.
Proof.
  intros.
  unfold csem in H.
  repeat destruct_ex_and.
  pose proof H1 as G.
  apply stmt_list_csem_outputs in G.
  unfold csem'.
  rewrite G.
  pose proof H1 as F.
  apply stmt_list_csem_env_extends in F.
  destruct F as [ev'' F]; subst.
  rewrite mk_ins_inputs; auto.
  repeat split; auto.
  exists x0.
  exists x1.
  intuition.
  eexists; eauto.
Qed.
