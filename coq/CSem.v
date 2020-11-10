(** * Concrete Semantics *)

Require Import ListSet Nat Bool Program Monad Proc Alg Sem SemTactics.
Import List.ListNotations.
Open Scope list_scope.

(** Concrete message algebra

    Notice that encryptions take one more argument as compared with
    encryptions in the message algebra.  The extra argument is some
    randomness.  See [CEn].  This is how probabilistic encryption is
    modeled.

    The key theorem in this library is [csem_sem], which states that
    whenever there is a run in the concrete executions semantics,
    there is a corresponding run in the abstract execution semantics. *)

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

Definition calg_dec:
  forall x y: calg, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality;
    try apply string_dec;
    decide equality.
Defined.
Hint Resolve calg_dec : core.

(** Concrete event *)

Inductive cevt: Set :=
| CSd: var -> calg -> cevt      (* Send *)
| CRv: var -> calg -> cevt.     (* Recv *)

Definition cevt_dec:
  forall x y: cevt, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
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

Lemma has_enc_inv:
  forall x,
    has_enc (inv x) = has_enc x.
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

(** Check the sort of an element in the concrete algebra. *)

Inductive csort_check: sort -> calg -> Prop :=
| CText_check: forall v,
    csort_check Text (CTx v)
| CData_check: forall v,
    csort_check Data (CDt v)
| CName_check: forall v,
    csort_check Name (CNm v)
| CSkey_check: forall k,
    csort_check Skey (CSk k)
| CAkey_check: forall k,
    csort_check Akey (CAk k)
| CIkey_check: forall k,
    csort_check Ikey (CIk k)
| CChan_check: forall v,
    csort_check Chan (CCh v)
| CMesg_check: forall a,
    csort_check Mesg a.
Hint Constructors csort_check : core.

Lemma sort_check_equiv:
  forall (s: sort) (c: calg),
    csort_check s c <-> sort_check s (to_alg c).
Proof.
  split; intros; destruct c; simpl in *; inv H; auto.
Qed.

Lemma inv_to_alg:
  forall x,
    inv (to_alg x) = to_alg (cinv x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

(** The semantics of an expression

   This predicate captures the semantics of a let binding

<<
   Parmeters:
   cenv:      Input environment
   list cevt: Input trace
   list calg: Input list of uniques
   list nat:  Input list of random values
   expr:      Expression code fragment
   decl:      Declaration to be bound by the value of the expression
   cenv:      Output environment
   list cevt: Output trace
   list calg: Output list of uniques
   list nat:  Output list of random values
>>

*)

Inductive expr_csem: cenv -> list cevt -> list calg -> list nat ->
                     expr -> decl -> cenv -> list cevt ->
                     list calg -> list nat -> Prop :=
| CExpr_tagg: forall ev tr us rs x s v,
    csort_check s (CTg x) ->
    expr_csem ev tr us rs (Tagg x) (v, s) ((v, CTg x) :: ev) tr us rs
| CExpr_hash: forall ev tr us rs x a v s,
    lookup x ev = Some a ->
    csort_check s (CHs a) ->
    expr_csem ev tr us rs (Hash x) (v, s) ((v, CHs a) :: ev) tr us rs
| CExpr_pair: forall ev tr us rs x y a b v s,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    csort_check s (CPr a b) ->
    expr_csem ev tr us rs (Pair x y) (v, s) ((v, CPr a b) :: ev) tr us rs
| CExpr_encr_prob: forall ev tr us rs x y r a b v s,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    csort_check s (CEn r a b) ->
    expr_csem ev tr us (r :: rs) (Encr x y) (v, s)
              ((v, CEn r a b) :: ev) tr us rs
| CExpr_encr_zero: forall ev tr us x y a b v s,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    csort_check s (CEn 0 a b) ->
    expr_csem ev tr us [] (Encr x y) (v, s) ((v, CEn 0 a b) :: ev) tr us []
| CExpr_frst: forall ev tr us rs x a b v s,
    lookup x ev = Some (CPr a b) ->
    csort_check s a ->
    expr_csem ev tr us rs (Frst x) (v, s) ((v, a) :: ev) tr us rs
| CExpr_scnd: forall ev tr us rs x a b v s,
    lookup x ev = Some (CPr a b) ->
    csort_check s b ->
    expr_csem ev tr us rs (Scnd x) (v, s) ((v, b) :: ev) tr us rs
| CExpr_decr: forall ev tr us rs x y r a b v s,
    lookup x ev = Some (CEn r a b) ->
    lookup y ev = Some (cinv b) ->
    csort_check s a ->
    expr_csem ev tr us rs (Decr x y) (v, s) ((v, a) :: ev) tr us rs
| CExpr_nonce: forall ev tr us rs a v s,
    csort_check s a ->
    expr_csem ev tr (a :: us) rs Nonce (v, s)
             ((v, a) :: ev) tr us rs
| CExpr_recv: forall ev tr us rs a c d v s,
    lookup c ev = Some (CCh d) ->
    csort_check s a ->
    expr_csem ev (CRv d a :: tr) us rs (Recv c) (v, s)
             ((v, a) :: ev) tr us rs.
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

Local Ltac lookup_and_sort_check :=
  repeat match goal with
         | [ H: lookup _ _ = Some _ |- _ ] =>
           apply lookup_ev in H; simpl in H
         | [ H: csort_check _ _ |- _ ] =>
           rewrite sort_check_equiv in H
         end.

(** Main theorem about expressions *)

Theorem expr_csem_expr_sem:
  forall ev tr us rs exp dcl ev' tr' us' rs',
    expr_csem ev tr us rs exp dcl ev' tr' us' rs' ->
    expr_sem (to_env ev) (map to_evt tr) (map to_alg us)
             exp dcl
             (to_env ev') (map to_evt tr') (map to_alg us').
Proof.
  intros. destruct dcl as [v s].
  inv H; simpl; auto; lookup_and_sort_check; eauto.
  rewrite <- inv_to_alg in H8.
  eauto.
Qed.

(** The semantics of statements

<<
   Parmeters:
   cenv:      Input environment
   list cevt: Input trace
   list calg: Input list of uniques
   list nat:  Input list of random values
   list calg: Input list of outputs
   cenv:      Output environment
   stmts:     Statements
>>
*)

Inductive stmts_csem: cenv -> list cevt -> list calg ->
                      list nat -> list calg ->
                      cenv -> stmts -> Prop :=
| CStmts_return: forall ev rs outs vs,
    map_m (flip lookup ev) vs = Some outs ->
    stmts_csem ev [] [] rs outs ev (Return vs)
| CStmts_bind: forall ev tr us rs outs exp dcl ev'' stmts ev' tr' us' rs',
    expr_csem ev tr us rs exp dcl ev' tr' us' rs' ->
    stmts_csem ev' tr' us' rs' outs ev'' stmts ->
    stmts_csem ev tr us rs outs ev'' (Bind dcl exp stmts)
| CStmts_send: forall ev tr us rs outs c d x a ev' stmts,
    lookup c ev = Some (CCh d) ->
    lookup x ev = Some a ->
    stmts_csem ev tr us rs outs ev' stmts ->
    stmts_csem ev (CSd d a :: tr) us rs outs ev' (Send c x stmts)
| CStmts_same: forall ev tr us rs outs ev' stmts x y a b,
    lookup x ev = Some a ->
    lookup y ev = Some b ->
    a = b ->                    (* Sameness check *)
    has_enc (to_alg a) = false -> (* For probabilistic encryption *)
    stmts_csem ev tr us rs outs ev' stmts ->
    stmts_csem ev tr us rs outs ev' (Same x y stmts).
Hint Constructors stmts_csem : core.

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

(** Main theorem about statements *)

Theorem stmts_csem_stmts_sem:
  forall ev tr us rs outs ss ev',
      stmts_csem ev tr us rs outs ev' ss ->
      stmts_sem (to_env ev) (map to_evt tr) (map to_alg us)
                (map to_alg outs) (to_env ev') ss.
Proof.
  intros; induction H; auto; lookup_and_sort_check; eauto.
  - apply Stmts_return.
    apply map_m_lookup_cev; auto.
  - destruct dcl as [v s].
    apply expr_csem_expr_sem in H; eauto.
  - apply Stmts_send; auto.
  - subst. eauto.
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
    csort_check s x ->
    cins_inputs ds xs ->
    cins_inputs ((v, s) :: ds) (x :: xs).
Hint Constructors cins_inputs : core.

Lemma cins_ins_inputs:
  forall ds cxs,
    cins_inputs ds cxs -> ins_inputs ds (map to_alg cxs).
Proof.
  intros; induction H; simpl; auto.
  apply sort_check_equiv in H; auto.
Qed.

(** Definition of the concrete semantics *)

Definition csem (p: proc) (rs: list nat) (cev: cenv) (e: role): Prop :=
  exists cins,
    inputs e = map to_alg cins /\
    cins_inputs (ins p) cins /\
    exists ctr cus couts,
      let ev_in := mk_cenv (ins p) cins in
      stmts_csem ev_in ctr cus rs couts cev (body p) /\
      trace e = map to_evt ctr /\
      uniqs e = map to_alg cus /\
      outputs e = map to_alg couts.

(** Main theorem about the concrete semantics *)

Theorem csem_sem:
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
  apply stmts_csem_stmts_sem in H1.
  rewrite mk_cenv_env in H1.
  unfold sem.
  repeat match goal with
         | [ H: _ e = map _ _ |- _ ] =>
           rewrite H
         end.
  split; auto.
Qed.
