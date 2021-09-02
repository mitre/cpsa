(* Substitition

Copyright (c) 2021 The MITRE Corporation

This program is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California. *)

(** * Substitition

    This library is a companion to the [Match] library.  It provides a
    substitution function [subst_term] such that when [match_term]
    matches [x] to [y] and produces substitution [sb], then
    [subst_term sb x] equals [y]. *)

Require Import FunInd String List Nat Bool Arith.
Require Import Preamble Monad Alg Match.

Definition subst_skey (sb: sbst) (x: skey): skey :=
  match x with
  | Sv v =>
    match lookup v sb with
    | Some (Sk y) => y
    | _ => x
    end
  | Lt u v =>
    let x :=
        match lookup u sb with
        | Some (Nm x) => x
        | _ => u
        end in
    let y :=
        match lookup v sb with
        | Some (Nm y) => y
        | _ => v
        end in
    Lt x y
  end.

Definition subst_akey (sb: sbst) (x: akey): alg :=
  match x with
  | Av v =>
    match lookup v sb with
    | Some (Ak y) => Ak y
    | Some (Ik y) => Ik y
    | _ => Ak x
    end
  | Pb v =>
    match lookup v sb with
    | Some (Nm u) => Ak (Pb u)
    | _ => Ak x
    end
  | Pb2 s v =>
    match lookup v sb with
    | Some (Nm u) => Ak (Pb2 s u)
    | _ => Ak x
    end
  end.

(** Definition of substitution *)

Fixpoint subst_term (sb: sbst) (x: alg): alg :=
  match x with
  | Tx v =>
    match lookup v sb with
    | Some (Tx u) => Tx u
    | _ => x
    end
  | Dt v =>
    match lookup v sb with
    | Some (Dt u) => Dt u
    | _ => x
    end
  | Nm v =>
    match lookup v sb with
    | Some (Nm u) => Nm u
    | _ => x
    end
  | Sk x => Sk (subst_skey sb x)
  | Ak x => subst_akey sb x
  | Ik x => inv (subst_akey sb x)
  | Ch v =>
    match lookup v sb with
    | Some (Ch u) => Ch u
    | _ => x
    end
  | Mg v =>
    match lookup v sb with
    | Some y => y
    | None => x
    end
  | Tg s => x
  | Pr x y => Pr (subst_term sb x) (subst_term sb y)
  | En x y => En (subst_term sb x) (subst_term sb y)
  | Hs x => Hs (subst_term sb x)
  end.

(** ** Correctness of Substitution *)

Lemma extend_term_lookup:
  forall (sb sb': sbst) (v: var) (x: alg),
    extend_term sb v x = Some sb' ->
    lookup v sb' = Some x.
Proof.
  unfold extend_term.
  intros.
  alt_option_dec (lookup v sb) b G;
    rewrite G in H.
  - inv H; simpl; auto.
    rewrite Nat.eqb_refl; simpl; auto.
  - destruct (alg_dec x b); inv H; simpl; auto.
Qed.

Lemma lookup_extend_term_lookup:
  forall v x y z sb sb',
    lookup v sb = Some x ->
    extend_term sb y z = Some sb' ->
    lookup v sb' = Some x.
Proof.
  intros.
  unfold extend_term in H0.
  destruct (Nat.eq_dec y v) as [G|G]; subst.
  - rewrite H in H0.
    destruct (alg_dec z x) as [G|G]; subst; inv H0; auto.
  - alt_option_dec (lookup y sb) b F;
      rewrite F in H0.
    + inv H0; simpl.
      rewrite <- Nat.eqb_neq in G.
      rewrite G; auto.
    + destruct (alg_dec z b); subst.
      inv H0; auto.
      inv H0.
Qed.

Lemma lookup_match_skey_lookup:
  forall v x y z sb sb',
    lookup v sb = Some x ->
    match_skey sb y z = Some sb' ->
    lookup v sb' = Some x.
Proof.
  intros.
  unfold match_skey in H0.
  destruct y.
  - eapply lookup_extend_term_lookup in H0; eauto.
  - destruct z.
    + inv H0.
    + apply do_some in H0.
      repeat destruct_ex_and.
      eapply lookup_extend_term_lookup in H0; eauto.
      eapply lookup_extend_term_lookup in H1; eauto.
Qed.

Lemma lookup_match_akey_lookup:
  forall v x y z sb sb',
    lookup v sb = Some x ->
    match_akey sb y z = Some sb' ->
    lookup v sb' = Some x.
Proof.
  intros.
  unfold match_akey in H0.
  destruct y.
  - eapply lookup_extend_term_lookup in H0; eauto.
  - destruct z.
    + inv H0.
    + eapply lookup_extend_term_lookup in H0; eauto.
    + inv H0.
  - destruct z.
    + inv H0.
    + inv H0.
    + destruct (String.eqb_spec s s0); subst.
      * eapply lookup_extend_term_lookup in H; eauto.
      * inv H.
        inv H0.
Qed.

Functional Scheme match_term_ind :=
  Induction for match_term Sort Prop.

Lemma lookup_match_term_lookup:
  forall v x y z sb sb',
    lookup v sb = Some x ->
    match_term sb y z = Some sb' ->
    lookup v sb' = Some x.
Proof.
  intros.
  revert H0.
  revert H.
  revert sb'.
  revert x.
  revert v.
  functional induction (match_term sb y z); intros;
    try match goal with
        | [ H: None = Some _ |- _ ] => inv H
        | [ H: extend_term _ _ _ = Some _ |- _ ] =>
          eapply lookup_extend_term_lookup in H; eauto
        | [ H: match_skey _ _ _ = Some _ |- _ ] =>
          eapply lookup_match_skey_lookup in H; eauto
        | [ H: match_akey _ _ _ = Some _ |- _ ] =>
          eapply lookup_match_akey_lookup in H; eauto
        end.
  - inv H0; auto.
  - eapply IHo0; eauto.
  - eapply IHo0; eauto.
  - eapply IHo; eauto.
Qed.

Lemma match_match_subst_skey:
  forall w x y z sb sb' sb'',
    match_skey sb w y = Some sb' ->
    match_term sb' x z = Some sb'' ->
    subst_skey sb'' w = y.
Proof.
  intros.
  unfold match_skey in H.
  destruct w.
  - apply extend_term_lookup in H.
    eapply lookup_match_term_lookup in H; eauto.
    simpl; rewrite H; auto.
  - destruct y.
    * inv H.
    * apply do_some in H.
      repeat destruct_ex_and.
      apply extend_term_lookup in H.
      eapply lookup_extend_term_lookup in H; eauto.
      eapply lookup_match_term_lookup in H; eauto.
      apply extend_term_lookup in H1.
      eapply lookup_match_term_lookup in H1; eauto.
      simpl.
      rewrite H.
      rewrite H1; auto.
Qed.

Lemma match_match_subst_akey:
  forall w x y z sb sb' sb'',
    match_akey sb w y = Some sb' ->
    match_term sb' x z = Some sb'' ->
    subst_akey sb'' w = (Ak y).
Proof.
  intros.
  unfold match_akey in H.
  destruct w.
  - apply extend_term_lookup in H.
    eapply lookup_match_term_lookup in H; eauto.
    simpl; rewrite H; auto.
  - destruct y.
    * inv H.
    * apply extend_term_lookup in H.
      eapply lookup_match_term_lookup in H; eauto.
      simpl.
      rewrite H; auto.
    * inv H.
  - destruct y.
    * inv H.
    * inv H.
    * destruct (String.eqb_spec s s0); subst.
      -- apply extend_term_lookup in H.
         eapply lookup_match_term_lookup in H; eauto.
         simpl.
         rewrite H; auto.
      -- inv H.
Qed.

(** The proof of this lemma contains two tricky steps. *)

Lemma match_match_subst_term:
  forall w x y z sb sb' sb'',
    match_term sb w y = Some sb' ->
    match_term sb' x z = Some sb'' ->
    subst_term sb'' w = y.
Proof.
  intros w x y z sb sb' sb''.
  revert sb'.
  revert z.
  revert x.
  functional induction (match_term sb w y); intros; simpl;
    try match goal with
        | [ H: None = Some _ |- _ ] => inv H
        | [ H: extend_term _ _ _ = Some _ |- _ ] =>
          apply extend_term_lookup in H;
          eapply lookup_match_term_lookup in H; eauto;
            match goal with
            | [ H: lookup _ _ = Some _ |- _ ] =>
              rewrite H; simpl; auto
            end
        | [ H: match_akey _ _ _ = Some _ |- _ ] =>
          eapply match_match_subst_akey in H; eauto;
            match goal with
            | [ H: lookup _ _ = Some _ |- _ ] =>
              rewrite H; simpl; auto
            end
        end.
  - eapply match_match_subst_skey in H; eauto.
    rewrite H; auto.
  - eapply match_match_subst_akey in H; eauto.
    simpl in H.
    apply eq_sym.
    rewrite inv_swap.
    simpl; auto.
  - eapply match_match_subst_akey in H; eauto.
    simpl in H.
    apply eq_sym.
    rewrite inv_swap.
    simpl; auto.
  - eapply match_match_subst_akey in H; eauto.
    simpl in H.
    apply eq_sym.
    rewrite inv_swap.
    simpl; auto.
  - rewrite String.eqb_eq in e1; subst; auto.
  - (* This in the tricky part *)
    apply IHo with (x := Pr w x)(z := Pr y0 z) in e1; auto.
    + eapply IHo0 in H; eauto.
      rewrite H.
      rewrite e1; auto.
    + simpl; auto.
      rewrite H; auto.
  - (* This in the tricky part *)
    apply IHo with (x := En w x)(z := En y0 z) in e1; auto.
    + eapply IHo0 in H; eauto.
      rewrite H.
      rewrite e1; auto.
    + simpl; auto.
      rewrite H; auto.
  - eapply IHo in H; eauto.
    rewrite H; auto.
Qed.

Lemma match_subst_skey:
  forall x y sb sb',
    match_skey sb x y = Some sb' ->
    subst_skey sb' x = y.
Proof.
  intros.
  unfold match_skey in H.
  unfold subst_skey.
  destruct x; simpl in *; auto.
  - apply extend_term_lookup in H.
    rewrite H; auto.
  - destruct y; simpl in *; auto.
    + inv H.
    + apply do_some in H.
      repeat destruct_ex_and.
      apply extend_term_lookup in H.
      eapply lookup_extend_term_lookup in H; eauto.
      apply extend_term_lookup in H0.
      rewrite H0.
      rewrite H; auto.
Qed.

Lemma match_subst_akey:
  forall x y sb sb',
    match_akey sb x y = Some sb' ->
    subst_akey sb' x = Ak y.
Proof.
  intros.
  unfold match_akey in H.
  unfold subst_akey.
  destruct x; simpl in *; auto.
  - apply extend_term_lookup in H.
    rewrite H; auto.
  - destruct y; simpl in *; auto.
    + inv H.
    + apply extend_term_lookup in H.
      rewrite H; auto.
    + inv H.
  - destruct y; simpl in *; auto.
    + inv H.
    + inv H.
    + destruct (String.eqb_spec s s0); subst.
      apply extend_term_lookup in H.
      rewrite H; auto.
      inv H.
Qed.

(** The main correctness theorem *)

Theorem match_subst_term:
  forall x y sb sb',
    match_term sb x y = Some sb' ->
    subst_term sb' x = y.
Proof.
  intros x y sb.
  functional induction (match_term sb x y); intros;
    try match goal with
        | [ H: None = Some _ |- _ ] => inv H
        | [ H: extend_term _ _ _ = Some _ |- _ ] =>
          apply extend_term_lookup in H;
            simpl; rewrite H; auto
        | [ H: match_skey _ _ _ = Some _ |- _ ] =>
          apply match_subst_skey in H;
            simpl; rewrite H; auto
        | [ H: match_akey _ _ _ = Some _ |- _ ] =>
          apply match_subst_akey in H;
            unfold subst_akey in H;
            simpl; rewrite H; auto
        end.
  - apply String.eqb_eq in e1; subst.
    simpl; auto.
  - simpl.
    pose proof H as G.
    eapply match_match_subst_term in H; eauto.
    apply IHo0 in G.
    rewrite G.
    rewrite H; auto.
  - simpl.
    pose proof H as G.
    eapply match_match_subst_term in H; eauto.
    apply IHo0 in G.
    rewrite G.
    rewrite H; auto.
  - simpl.
    apply IHo in H; auto.
    rewrite H; auto.
Qed.
