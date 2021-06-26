(** This library contains proofs that the semantics specified in
    [Roletran.Run] and [Roletran.Sem] agree. *)

Require Import FunInd List Bool Arith.
Require Import Preamble Proc Alg Sem Alt_sem Run.
Open Scope nat_scope.

Lemma expr_sem_implies_run_expr:
  forall ev tr us exp val tr' us',
    expr_sem ev tr us exp val tr' us' ->
    run_expr (mkRSt ev tr us) exp =
    Some (mkRSt ev tr' us', val).
Proof.
  intros.
  inv H; simpl;
    repeat match goal with
           | [ H: lookup _ _ = Some _ |- _ ] => rewrite H
           end; auto.
  - rewrite H2; simpl.
    destruct (bool_dec (alg_eqb (inv b) (inv b)) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite alg_eq_correct; auto.
  - rewrite <- beq_nat_refl; auto.
Qed.

Lemma run_expr_implies_expr_sem:
  forall rst exp val rst',
    run_expr rst exp = Some (rst', val) ->
    expr_sem (renv rst) (rtr rst) (runiqs rst)
             exp val (rtr rst') (runiqs rst') /\
    renv rst = renv rst'.
Proof.
  intros.
  destruct exp; simpl in H.
  - inv H; simpl; auto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H; inv H; auto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct (option_dec (lookup n0 (renv rst))) as [F|F].
      * rewrite F in H; inv H.
      * destruct F as [c F]; rewrite F in H; inv H; auto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct (option_dec (lookup n0 (renv rst))) as [F|F].
      * rewrite F in H; inv H.
      * destruct F as [c F]; rewrite F in H; inv H; auto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      split; auto.
      eapply Expr_frst; eauto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      split; auto.
      eapply Expr_scnd; eauto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G]; rewrite G in H.
      destruct b; inv H.
      destruct (option_dec (lookup n0 (renv rst))) as [F|F].
      * rewrite F in H1; inv H1; destruct b; inv H0.
      * destruct F as [c F]; rewrite F in H1.
        destruct (alt_bool_dec (negb (has_enc c))) as [D|D];
          rewrite D in H1; simpl in H1.
        destruct (bool_dec (alg_eqb c (inv b2)) true) as [E|E].
        -- rewrite E in H1; inv H1.
           apply alg_eq_correct in E; subst.
           split; auto.
           eapply Expr_decr; eauto.
           apply negb_true_iff in D; auto.
        -- rewrite not_true_iff_false in E.
           rewrite E in H1; inv H1.
        -- inv H1.
  - destruct (runiqs rst); inv H; auto.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [c G]; rewrite G in H.
      destruct (rtr rst).
      * inv H.
      * destruct e.
        -- inv H.
        -- destruct c; inv H.
           destruct (bool_dec (n1 =? n0) true) as [F|F].
           ++ rewrite F in H1; inv H1.
              apply beq_nat_true in F; subst; auto.
           ++ rewrite not_true_iff_false in F.
              rewrite F in H1; inv H1.
Qed.

Lemma type_check_reflect:
  forall (x: alg) (t: type),
    type_check x t = true <-> Sem.type_check t x.
Proof.
  intros.
  unfold type_check.
  rewrite orb_true_iff.
  repeat rewrite type_eq_correct.
  rewrite Sem.type_check_type_of; intuition.
Qed.

Lemma stmt_sem_implies_run_stmt:
  forall ev tr us cmd ev' tr' us',
    stmt_sem ev tr us cmd ev' tr' us' ->
    run_stmt (mkRSt ev tr us) cmd =
    Some (mkRSt ev' tr' us').
Proof.
  intros.
  inv H.
  - apply expr_sem_implies_run_expr in H0.
    rewrite <- type_check_reflect in H1.
    simpl.
    rewrite H0.
    rewrite H1; auto.
  - simpl.
    rewrite H0.
    rewrite <- beq_nat_refl; auto.
    rewrite H1.
    destruct (bool_dec (alg_eqb a a) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite alg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    simpl.
    destruct (bool_dec (alg_eqb b b) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite alg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    destruct (bool_dec (alg_eqb (Sk (Lt b c))
                                (Sk (Lt b c))) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite alg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    simpl.
    destruct (bool_dec (alg_eqb (inv b) (inv b)) true) as [G|G].
    + rewrite G; auto.
    + contradiction G.
      rewrite alg_eq_correct; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    simpl.
    unfold akey_eqb.
    destruct (akey_dec (Pb b) (Pb b)) as [G|G]; auto.
    contradict G; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    simpl.
    unfold akey_eqb.
    destruct (akey_dec (Pb b) (Pb b)) as [G|G]; auto.
    contradict G; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    unfold akey_eqb.
    destruct (akey_dec (Pb2 s b) (Pb2 s b)) as [G|G]; auto.
    contradict G; auto.
  - simpl.
    rewrite H0.
    rewrite H1.
    rewrite H2.
    unfold akey_eqb.
    destruct (akey_dec (Pb2 s b) (Pb2 s b)) as [G|G]; auto.
    contradict G; auto.
Qed.

Lemma run_stmt_implies_stmt_sem:
  forall rst cmd rst',
    run_stmt rst cmd = Some rst' ->
    stmt_sem (renv rst) (rtr rst) (runiqs rst)
             cmd (renv rst') (rtr rst') (runiqs rst').
Proof.
  intros; destruct cmd; simpl in *.
  - inv H.
  - destruct d as [v t].
    destruct (option_dec (run_expr rst e)) as [G|G].
    + rewrite G in H; inv H.
    + destruct G as [b G].
      destruct b as [st x].
      rewrite G in H.
      destruct (bool_dec (type_check x t) true) as [F|F].
      * rewrite F in H.
        inv H; simpl.
        rewrite type_check_reflect in F.
        apply run_expr_implies_expr_sem in G; auto.
        destruct G.
        rewrite <- H0.
        eapply Stmt_bind; eauto.
      * rewrite not_true_iff_false in F.
        rewrite F in H; inv H.
  - destruct (rtr rst).
    + inv H.
    + destruct e.
      * destruct (option_dec (lookup n (renv rst))) as [G|G].
        -- rewrite G in H; inv H.
        -- destruct G.
           rewrite H0 in H.
           destruct x; inv H.
           destruct (bool_dec (n2 =? n1) true) as [G|G].
           ++ rewrite G in H2; inv H2.
              apply beq_nat_true in G; subst.
              destruct (option_dec (lookup n0 (renv rst))) as [G|G].
              ** rewrite G in H1; inv H1.
              ** destruct G.
                 rewrite H in H1.
                 destruct (bool_dec (alg_eqb a x) true) as [F|F].
                 --- rewrite F in H1; inv H1.
                     rewrite alg_eq_correct in F; subst.
                     apply Stmt_send; auto.
                 --- rewrite not_true_iff_false in F.
                     rewrite F in H1; inv H1.
           ++ rewrite not_true_iff_false in G.
              rewrite G in H2; inv H2.
      * inv H.
  - destruct (option_dec (lookup n (renv rst))) as [G|G].
    + rewrite G in H; inv H.
    + destruct G.
      rewrite H0 in H.
      destruct (option_dec (lookup n0 (renv rst))) as [G|G].
      * rewrite G in H; inv H.
      * destruct G.
        rewrite H1 in H.
        destruct (alt_bool_dec (has_enc x)) as [F|F];
          rewrite F in H; simpl in H.
        inv H.
        destruct (bool_dec (alg_eqb x x0) true) as [G|G].
        -- rewrite G in H; inv H.
           apply alg_eq_correct in G; subst.
           eapply Stmt_same; eauto.
        -- rewrite not_true_iff_false in G.
           rewrite G in H; inv H.
  - alt_option_dec (lookup n (renv rst)) v G;
      rewrite G in H.
    + inv H.
    + alt_option_dec (lookup n0 (renv rst)) u F;
        rewrite F in H.
      * inv H.
      * alt_option_dec (lookup n1 (renv rst)) w E;
          rewrite E in H.
        -- inv H.
        -- destruct u; inv H.
           destruct w; inv H1.
           destruct (alt_bool_dec (alg_eqb v (Sk (Lt n2 n3)))) as [D|D];
             rewrite D in H0.
           ++ rewrite alg_eq_correct in D; subst.
              inv H0.
              eapply Stmt_ltkp; eauto.
           ++ inv H0.
  - alt_option_dec (lookup n (renv rst)) x G;
      rewrite G in H.
    + inv H.
    + alt_option_dec (lookup n0 (renv rst)) y F;
        rewrite F in H.
      * inv H.
      * destruct (alt_bool_dec (has_enc x)) as [D|D];
          rewrite D in H; simpl in H.
        inv H.
        destruct (alt_bool_dec (alg_eqb x (inv y))) as [E|E];
          rewrite E in H.
        -- inv H.
           apply alg_eq_correct in E.
           eapply Stmt_invp; eauto.
        -- inv H.
  - alt_option_dec (lookup n (renv rst)) x G;
      rewrite G in H.
    + inv H.
    + alt_option_dec (lookup n0 (renv rst)) y F;
        rewrite F in H.
      * inv H.
      * destruct x; inv H.
        -- destruct y; inv H1.
           unfold akey_eqb in H0.
           destruct (akey_dec a (Pb n1)) as [E|E]; subst.
           ++ inv H0.
              eapply Stmt_pub_namp; eauto.
           ++ inv H0.
        -- destruct y; inv H1.
           unfold akey_eqb in H0.
           destruct (akey_dec a (Pb n1)) as [E|E]; subst.
           ++ inv H0.
              eapply Stmt_priv_namp; eauto.
           ++ inv H0.
  - alt_option_dec (lookup n (renv rst)) x G;
      rewrite G in H.
    + inv H.
    + alt_option_dec (lookup n0 (renv rst)) y F;
        rewrite F in H.
      * inv H.
      * alt_option_dec (lookup n1 (renv rst)) z E;
          rewrite E in H.
        -- inv H.
        -- destruct x; inv H.
           ++ destruct y; inv H1.
              destruct z; inv H0.
              unfold akey_eqb in H1.
              destruct (akey_dec a (Pb2 s n2)) as [D|D].
              ** inv H1.
                 eapply Stmt_pub_nm2p; eauto.
              ** inv H1.
           ++ destruct y; inv H1.
              destruct z; inv H0.
              unfold akey_eqb in H1.
              destruct (akey_dec a (Pb2 s n2)) as [D|D].
              ** inv H1.
                 eapply Stmt_priv_nm2p; eauto.
              ** inv H1.
Qed.

Lemma stmt_list_sem_implies_run_stmts:
  forall ev_in tr us outs stmts ev,
    stmt_list_sem ev_in tr us outs stmts ev ->
    run_stmts (mkRSt ev_in tr us) stmts = Some (ev, outs).
Proof.
  intros.
  induction H.
  - unfold Basics.flip in H.
    simpl.
    rewrite H; auto.
  - apply stmt_sem_implies_run_stmt in H.
    simpl; rewrite H.
    destruct stmt; simpl; simpl in H; auto.
    inv H.
Qed.

Functional Scheme run_stmts_ind :=
  Induction for run_stmts Sort Prop.

Lemma run_stmts_implies_stmt_list_sem:
  forall rst stmts ev outs,
    run_stmts rst stmts = Some (ev, outs) ->
    stmt_list_sem (renv rst) (rtr rst) (runiqs rst) outs stmts ev.
Proof.
  intros.
  functional induction (run_stmts rst stmts); inv H.
  - rewrite e2.
    rewrite e3.
    apply Stmt_return; auto.
  - inv e2.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
  - apply run_stmt_implies_stmt_sem in e1.
    apply IHo in H1.
    eapply Stmt_pair; eauto.
Qed.

Lemma sem_bind_inputs_aux:
  forall ds xs ev,
    ins_inputs ds xs ->
    bind_inputs ds xs ev = Some (rev (mk_env ds xs) ++ ev).
Proof.
  intros ds xs ev H.
  revert ev.
  induction H; intros; simpl; auto.
  rewrite <- type_check_reflect in H.
  rewrite H.
  rewrite IHins_inputs; simpl; auto.
  repeat rewrite <- app_assoc.
  repeat rewrite rev_app_distr; simpl.
  simpl; auto.
Qed.

Lemma sem_bind_inputs:
  forall ds xs,
    ins_inputs ds xs ->
    bind_inputs ds xs nil = Some (rev (mk_env ds xs)).
Proof.
  intros.
  rewrite sem_bind_inputs_aux; auto.
  rewrite app_nil_r; auto.
Qed.

Functional Scheme bind_inputs_ind :=
  Induction for bind_inputs Sort Prop.

Lemma sem_ins_inputs_aux:
  forall ds xs ev ev',
    bind_inputs ds xs ev = Some ev' ->
    ins_inputs ds xs.
Proof.
  intros.
  functional induction (bind_inputs ds xs ev); simpl; auto; inv H.
  apply type_check_reflect in e2.
  apply Ins_inputs_pair; auto.
Qed.

Lemma sem_ins_inputs:
  forall ds xs ev,
    bind_inputs ds xs nil = Some ev ->
    ins_inputs ds xs /\ ev = rev (mk_env ds xs).
Proof.
  intros.
  assert (G: ins_inputs ds xs).
  - eapply sem_ins_inputs_aux; eauto.
  - split; auto.
    pose proof (sem_bind_inputs ds xs).
    apply H0 in G.
    rewrite G in H.
    inv H; auto.
Qed.

Lemma sem'_implies_run:
  forall (p: proc) (ev: env) (tr: list evt) (us: list alg),
    sem' p ev tr us ->
    exists outs,
      get_outs ev (body p) = Some outs /\
      run p (get_ins ev (ins p)) tr us = Some (ev, outs).
Proof.
  intros.
  unfold sem' in H.
  repeat destruct_ex_and.
  exists x.
  split; auto.
  unfold run.
  rewrite sem_bind_inputs; auto.
  rewrite rev_involutive.
  eapply stmt_list_sem_implies_run_stmts in H1; eauto.
Qed.

(** The semantics as a predicate implies the semantics as a function. *)

Theorem sem_implies_run:
  forall (p: proc) (ev: env) (ex: role),
    sem p ev ex ->
    run p (inputs ex) (trace ex) (uniqs ex) =
    Some (ev, outputs ex).
Proof.
  intros.
  erewrite sem_implies_inputs; eauto.
  pose proof H as G.
  apply sem_implies_sem' in H.
  apply sem_implies_outputs in G.
  unfold sem' in H.
  repeat destruct_ex_and.
  rewrite G in H0.
  inv H0.
  apply sem_bind_inputs in H.
  apply stmt_list_sem_implies_run_stmts in H1.
  unfold run.
  rewrite H; auto.
  rewrite rev_involutive; auto.
Qed.

(** The semantics as a function implies the semantics as a predicate. *)

Theorem run_implies_sem':
  forall p tr us ev outs,
    run p (get_ins ev (ins p)) tr us = Some (ev, outs) ->
    sem' p ev tr us.
Proof.
  intros.
  unfold run in H.
  destruct (option_dec (bind_inputs (ins p) (get_ins ev (ins p)) nil)) as [G|G].
  - rewrite G in H; inv H.
  - destruct G as [ev' G].
    rewrite G in H.
    apply sem_ins_inputs in G.
    destruct G; subst.
    rewrite rev_involutive in H.
    unfold sem'.
    split; auto.
    exists outs.
    eapply run_stmts_implies_stmt_list_sem in H; eauto.
    split; auto.
    apply stmt_list_sem_implies_outputs in H; auto.
Qed.
