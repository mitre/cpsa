(* Derivability

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * Derivability *)

Require Import List ListSet Bool Lia Alg Sem_tactics.

(** [derives pub t] when [t] can be derived using the terms in [pub]. *)

Inductive derives (pub: list alg): alg -> Prop :=
| Der_mem: forall x: alg, In x pub -> derives pub x
| Der_tagg: forall s, derives pub (Tg s)
| Der_pair: forall x y,
    derives pub x -> derives pub y -> derives pub (Pr x y)
| Der_encr: forall x y,
    derives pub x -> derives pub y -> derives pub (En x y)
| Der_hash: forall x,
    derives pub x -> derives pub (Hs x)
| Der_frst: forall x y, derives pub (Pr x y) -> derives pub x
| Der_scnd: forall x y, derives pub (Pr x y) -> derives pub y
| Der_decr: forall x y,
    derives pub (En x y) -> derives pub (inv y) -> derives pub x.
#[global]
Hint Constructors derives : core.

(* There is no good way to implement derives directly in code.  There
   is an easy way to do it with analyze-then-synthesize.  Here is the
   algorithm used in CPSA and in the role compiler:

synth(T, t): bool :=
  if t in T return true;
  if t = (t1, t2) return synth t1 && synth t2;
  if t = (enc t1 t2) return synth t1 && synth t2;
  if t = (hash t1) return synth t1;
  if t = "..." return true.

analyze(T): set of terms :=
  while T changes do
      let t = some element in T;
      if t = (t1, t2) then add t1 and t2 to T
      else if t = (enc t1 t2) and synth(T, invk(t2)) then add t1 to T;
   done;
   return T.
*)

(* synth pub t when t can be synthesized using the terms in pub. *)
Inductive synth (pub: alg -> Prop): alg -> Prop :=
| Synth_mem: forall x: alg, pub x -> synth pub x
| Synth_tag: forall i, synth pub (Tg i)
| Synth_pair: forall x y,
    synth pub x -> synth pub y -> synth pub (Pr x y)
| Synth_encr: forall x y,
    synth pub x -> synth pub y -> synth pub (En x y)
| Synth_hash: forall x,
    synth pub x -> synth pub (Hs x).
#[global]
Hint Constructors synth : core.

(* analyze pub t when t can be analyzed using the terms in pub. *)
Inductive analyze (pub: list alg): alg -> Prop :=
| Analyze_mem: forall x: alg, In x pub -> analyze pub x
| Analyze_frst: forall x y, analyze pub (Pr x y) -> analyze pub x
| Analyze_scnd: forall x y, analyze pub (Pr x y) -> analyze pub y
| Analyze_decr: forall x y,
    analyze pub (En x y) -> synth (analyze pub) (inv y) -> analyze pub x.

Theorem derives_implies_analyze_then_synth:
  forall pub x, derives pub x -> synth (analyze pub) x.
Proof.
  intros pub x H.
  induction H; auto.
  - apply Synth_mem; apply Analyze_mem; assumption.
  - inv IHderives; auto.
    apply Analyze_frst in H0.
    apply Synth_mem; assumption.
  - inv IHderives; auto.
    apply Analyze_scnd in H0.
    apply Synth_mem; assumption.
  - inv IHderives1; auto.
    apply Analyze_decr in H1; auto.
Qed.

(* Failed attempt that the final Theorem *)

Theorem analyze_then_synth_implies_derives:
  forall pub x, synth (analyze pub) x -> derives pub x.
Proof.
  intros pub x H.
  induction H; auto.
  induction H.
  - apply Der_mem; auto.
  - eapply Der_frst; eauto.
  - eapply Der_scnd; eauto.
  - eapply Der_decr; eauto.
    clear IHanalyze H x.
    (* HELP!!! *)
    give_up.
Abort.

(* Analyze stratified *)

Inductive analyze_strat (pub: list alg): nat -> alg -> Prop :=
| Analyze_strat_mem: forall x,
    In x pub ->
    analyze_strat pub 0 x
| Analyze_strat_incl: forall n x,
    analyze_strat pub n x ->
    analyze_strat pub (S n) x
| Analyze_strat_frst: forall n x y,
    analyze_strat pub n (Pr x y) ->
    analyze_strat pub (S n) x
| Analyze_strat_scnd: forall n x y,
    analyze_strat pub n (Pr x y) ->
    analyze_strat pub (S n) y
| Analyze_strat_decr: forall n x y,
    analyze_strat pub n (En x y) ->
    synth (analyze_strat pub n) (inv y) ->
    analyze_strat pub (S n) x.
#[global]
Hint Constructors analyze_strat : core.

Lemma analyze_strat_zero:
  forall pub t,
    analyze_strat pub 0 t <-> In t pub.
Proof.
  split; intros.
  - inv H; auto.
  - apply Analyze_strat_mem; auto.
Qed.

Lemma analyze_strat_zero_then_synth:
  forall pub t,
    synth (analyze_strat pub 0) t <-> synth (fun y => In y pub) t.
Proof.
  split; intros.
  - induction H; simpl; auto.
    rewrite analyze_strat_zero in H.
    apply Synth_mem; auto.
  - induction H; simpl; auto.
Qed.

Lemma synth_implies_derives:
  forall pub x, synth (fun y => In y pub) x -> derives pub x.
Proof.
  intros pub x H.
  induction H; auto.
Qed.

Lemma analyze_strat_derives:
  forall pub n t,
    synth (analyze_strat pub n) t -> derives pub t.
Proof.
  induction n; intros.
  - rewrite analyze_strat_zero_then_synth in H.
    apply synth_implies_derives; auto.
  - induction H; simpl; auto.
    inv H.
    + apply IHn.
      apply Synth_mem; auto.
    + apply Der_frst with (y := y); auto.
    + apply Der_scnd with (x := x0); auto.
    + apply IHn in H2.
      apply Der_decr with (y := y); auto.
Qed.

Lemma analyze_strat_monotonic_1:
  forall pub m t,
    synth (analyze_strat pub m) t ->
    synth (analyze_strat pub (S m)) t.
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Lemma analyze_strat_monotonic_2:
  forall pub m n t,
    synth (analyze_strat pub m) t ->
    synth (analyze_strat pub (n + m)) t.
Proof.
  intros.
  induction n; simpl; auto.
  apply analyze_strat_monotonic_1; auto.
Qed.

Lemma analyze_strat_monotonic:
  forall pub m n t,
    m <= n ->
    synth (analyze_strat pub m) t ->
    synth (analyze_strat pub n) t.
Proof.
  intros pub m n t H G.
  apply analyze_strat_monotonic_2 with (n := n - m) in G.
  assert (F: n - m + m = n).
  - lia.
  - rewrite F in G; auto.
Qed.

(* Reflection for synth *)

Fixpoint synthb (pub: list alg) t: bool :=
  set_mem alg_dec t pub ||
          match t with
          | Pr x y => synthb pub x && synthb pub y
          | En x y => synthb pub x && synthb pub y
          | Hs x => synthb pub x
          | Tg _ => true
          | _ => false
          end.

Lemma synthb_correct :
  forall pub x, synth (fun y => In y pub) x <-> synthb pub x = true.
Proof.
  split.
  - intro H.
    induction H; try apply orb_true_iff; intuition.
    destruct x; apply orb_true_iff; left; apply set_mem_correct2; auto.
  - induction x; intro H; simpl in H; apply orb_true_iff in H;
      destruct H; auto;
        try match goal with
            | [ H: set_mem alg_dec _ pub = true |- _ ] =>
              apply set_mem_correct1 in H; auto
            end; try intuition.
    + apply andb_true_iff in H.
      destruct H; auto.
    + apply andb_true_iff in H.
      destruct H; auto.
Qed.
