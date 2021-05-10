(** * The Message Algebra *)

Require Import FunInd Nat Bool DecBool Monad Proc.
(** printing <- #←# *)

Notation var := nat (only parsing).

(** Symmetric keys *)

Inductive skey: Set :=
| Sv: var -> skey               (* Variable as key *)
| Lt: var -> var -> skey.       (* Long term key of two names *)

(* An uninformative comment added to make coqdoc happy *)

Definition skey_dec:
  forall x y: skey, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
#[global]
Hint Resolve skey_dec : core.

(** Asymmetric keys *)

Inductive akey: Set :=
| Av: var -> akey               (* Variable as key *)
| Pb: var -> akey               (* Public key of name *)
| Pb2: string -> var -> akey.   (* Tagged public key of name *)

(* An uninformative comment added to make coqdoc happy *)

Definition akey_dec:
  forall x y: akey, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality;
    try apply string_dec;
    decide equality.
Defined.
#[global]
Hint Resolve akey_dec : core.

Definition akey_eqb x y: bool :=
  if akey_dec x y then
    true
  else
    false.

(** Message algebra *)

Inductive alg: Set :=
| Tx: var -> alg                (* Text *)
| Dt: var -> alg                (* Data *)
| Nm: var -> alg                (* Name *)
| Sk: skey -> alg               (* Symmetric key *)
| Ak: akey -> alg               (* Asymmetric key *)
| Ik: akey -> alg               (* Inverse asymmetric key *)
| Ch: var -> alg                (* Channel *)
| Mg: var -> alg                (* Message *)
| Tg: string -> alg             (* Tag *)
| Pr: alg -> alg -> alg         (* Pair *)
| En: alg -> alg -> alg         (* Encryption *)
| Hs: alg -> alg.               (* Hash *)

(* An uninformative comment added to make coqdoc happy *)

Definition alg_dec:
  forall x y: alg, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality;
    try apply string_dec;
    decide equality.
Defined.
#[global]
Hint Resolve alg_dec : core.

Definition alg_eqb x y: bool :=
  if alg_dec x y then
    true
  else
    false.

Lemma alg_eq_correct:
  forall x y,
    alg_eqb x y = true <-> x = y.
Proof.
  intros.
  unfold alg_eqb.
  destruct (alg_dec x y); subst; intuition.
  inversion H.
Qed.

Lemma alg_eq_complete:
  forall x y,
    alg_eqb x y = false <-> x <> y.
Proof.
  intros.
  unfold alg_eqb.
  destruct (alg_dec x y); subst; intuition.
Qed.

(** Event *)

Inductive evt: Set :=
| Sd: var -> alg -> evt         (* Send *)
| Rv: var -> alg -> evt.        (* Recv *)

(* An uninformative comment added to make coqdoc happy *)

Definition evt_dec:
  forall x y: evt, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
#[global]
Hint Resolve evt_dec : core.

(** The message communicated by an event *)

Definition evt_msg (e: evt): alg :=
  match e with
  | Sd _ t => t
  | Rv _ t => t
  end.

(** ** Kinds of Messages *)

(** Is [x] a basic value? *)

Definition is_basic (x: alg): bool :=
  match x with
  | Tx _ => true
  | Dt _ => true
  | Nm _ => true
  | Sk _ => true
  | Ak _ => true
  | Ik _ => true
  | _ => false
  end.

(** Is [x] a channel variable? *)

Definition is_chan (x: alg): bool :=
  match x with
  | Ch _ => true
  | _ => false
  end.

(** Is [x] a message variable? *)

Definition is_mesg_var (x: alg): bool :=
  match x with
  | Mg _ => true
  | _ => false
  end.

(** Is [x] a simple message, one that is not a pair, encryption, or a
    hash? *)

Definition is_simple (x: alg): bool :=
  match x with
  | Pr _ _ => false
  | En _ _ => false
  | Hs _ => false
  | _ => true
  end.

(** Is [x] an elementary message, one that is not a pair, encryption, a
    hash, or a tag? *)

Definition is_elem (x: alg): Prop :=
  match x with
  | Pr _ _ => False
  | En _ _ => False
  | Hs _ => False
  | Tg _ => False
  | _ => True
  end.

(** Is [x] not an elementary message? *)

Definition is_not_elem (x: alg): Prop :=
  match x with
  | Pr _ _ => True
  | En _ _ => True
  | Hs _ => True
  | Tg _ => True
  | _ => False
  end.

Lemma is_elem_dec:
  forall x: alg, {is_elem x} + {is_not_elem x}.
Proof.
  intros.
  unfold is_elem.
  unfold is_not_elem.
  destruct x; auto.
Qed.

Lemma alg_elem_ind:
  forall P: alg -> Prop,
    (forall x:alg, is_elem x -> P x) ->
    (forall s: string, P (Tg s)) ->
    (forall y: alg,
        P y ->
        forall z: alg,
          P z -> P (Pr y z)) ->
    (forall y: alg,
        P y ->
        forall z: alg, P (En y z)) ->
    (forall y: alg,
        P y -> P (Hs y)) ->
    forall x: alg, P x.
Proof.
  intros.
  induction x; simpl; auto; apply H; simpl; auto.
Qed.

(** ** Inverse of a Message *)

Definition inv (x: alg): alg :=
  match x with
  | Ak k => Ik k
  | Ik k => Ak k
  | k => k
  end.

Lemma inv_inv:
  forall (x: alg),
    inv (inv x) = x.
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Lemma inv_swap:
  forall (x y: alg),
    x = inv y <-> y = inv x.
Proof.
  split; intros; subst;
    rewrite inv_inv; auto.
Qed.

(** ** Type of an Algebra Term *)

Definition type_of (x: alg): type :=
  match x with
  | Tx _ => Text
  | Dt _ => Data
  | Nm _ => Name
  | Sk _ => Skey
  | Ak _ => Akey
  | Ik _ => Ikey
  | Mg _ => Mesg
  | Tg _ => Quot
  | Pr _ _ => Pair
  | En _ (Ak _) => Aenc
  | En _ (Ik _) => Ienc
  | En _ _ => Senc
  | Hs _ => Hash
  | Ch v => Chan
  end.

(** ** Is a Term Well Formed?

    When a term is well formed, variables must have a consistent type.
    An example of a term that is not well formed is
<<
    Pr (Tx 0) (Nm 0)
>>
    The type of variable 0 can't be both [Text] and [Name].
 *)

(** Lookup [v] in association list [e]. *)

Fixpoint lookup {A} (v: var) (e: list (var * A)): option A :=
  match e with
  | nil => None
  | (u, a) :: e =>
    if u =? v then
      Some a
    else
      lookup v e
  end.

(** Extend the decls if the extension is consistent with previous
    declarations. *)

Definition extend decls (v: var) (s: type): option (list decl) :=
  match lookup v decls with
  | None => Some ((v, s) :: decls)
  | Some s' =>
    if type_dec s' s then
      Some decls
    else                        (* Type clash! *)
      None
  end.

(** Is skey well formed? *)

Definition well_formed_skey decls (k: skey): option (list decl) :=
  match k with
  | Sv v => extend decls v Skey
  | Lt v v' =>
    ds <- extend decls v Name;;
    extend ds v' Name
  end.

(** Is akey well formed? *)

Definition well_formed_akey decls (k: akey): option (list decl) :=
  match k with
  | Av v => extend decls v Akey
  | Pb v =>  extend decls v Name
  | Pb2 c v =>  extend decls v Name
  end.

(** Is algebra term well formed?  For term [x], [well_formed [] x]
    returns the declarations for the variables that occur in x or
    [None] when the term is not well formed.  Note that channels are
    considered not well formed in this function. *)

Fixpoint well_formed decls (x: alg): option (list decl) :=
  match x with
  | Tx v => extend decls v Text
  | Dt v => extend decls v Data
  | Nm v => extend decls v Name
  | Sk k => well_formed_skey decls k
  | Ak k => well_formed_akey decls k
  | Ik k => well_formed_akey decls k
  | Ch v => None                (* Channels are forbidden *)
  | Mg v => extend decls v Mesg
  | Tg z => Some decls
  | Pr y z =>
    ds <- well_formed decls y;;
    well_formed ds z
  | En y z =>
    ds <- well_formed decls y;;
    well_formed ds z
  | Hs y => well_formed decls y
  end.

Definition well_formed_event decls (x: evt): option (list decl) :=
  match x with
  | Sd ch y =>
    ds <- extend decls ch Chan;;
    well_formed ds y
  | Rv ch y =>
    ds <- extend decls ch Chan;;
    well_formed ds y
  end.

(** ** Is a Term Well Typed?

    Like well formed except it does not extend its declarations. *)

Definition well_typed_var decls (v: var) (s: type): bool :=
  match lookup v decls with
  | None => false
  | Some s' => ifdec (type_dec s' s) true false
  end.

(** Is skey well typed? *)

Definition well_typed_skey decls (k: skey): bool :=
  match k with
  | Sv v => well_typed_var decls v Skey
  | Lt v v' => well_typed_var decls v Name &&
               well_typed_var decls v' Name
  end.

(** Is akey well typed? *)

Definition well_typed_akey decls (k: akey): bool :=
  match k with
  | Av v => well_typed_var decls v Akey
  | Pb v =>  well_typed_var decls v Name
  | Pb2 c v =>  well_typed_var decls v Name
  end.

(** Is algebra term well typed?  For term [x], [well_typed decl x]
    is true when [x] is true when it is well typed with respect to
    the declarations [decls].  Note that channels are considered not
    well typed in this function. *)

Fixpoint well_typed decls (x: alg): bool :=
  match x with
  | Tx v => well_typed_var decls v Text
  | Dt v => well_typed_var decls v Data
  | Nm v => well_typed_var decls v Name
  | Sk k => well_typed_skey decls k
  | Ak k => well_typed_akey decls k
  | Ik k => well_typed_akey decls k
  | Ch v => false               (* Channels are forbidden *)
  | Mg v => well_typed_var decls v Mesg
  | Tg z => true
  | Pr y z => well_typed decls y &&
              well_typed decls z
  | En y z => well_typed decls y &&
              well_typed decls z
  | Hs y => well_typed decls y
  end.

(** Is algebra term or channel well typed? *)

Definition well_typed_with_chan decls (x: alg): bool :=
  match x with
  | Ch v => well_typed_var decls v Chan
  | _ => well_typed decls x
  end.

(** ** Measure of a term *)

Fixpoint size (x: alg): nat :=
  match x with
  | Pr y z => S (size y + size z)
  | En y z => S (size y + size z)
  | Hs y => S (size y)
  | _ => 1
  end.

Lemma inv_size:
  forall x, size (inv x) = size x.
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

(** ** Origination *)

(** Carried by *)

Fixpoint cb (x y: alg): bool :=
  alg_eqb x y ||
          match y with
          | Pr a b => cb x a || cb x b
          | En a _ => cb x a
          | _ => false
          end.

Functional Scheme cb_ind :=
  Induction for cb Sort Prop.

Lemma cb_refl:
  forall x,
    cb x x = true.
Proof.
  intros.
  cut (alg_eqb x x = true); intros.
  - destruct x; simpl; rewrite H; auto.
  - apply alg_eq_correct; auto.
Qed.

Inductive carried_by: alg -> alg -> Prop :=
| Carried_by_refl:
    forall x, carried_by x x
| Carried_by_frst:
    forall x y z,
      carried_by z x ->
      carried_by z (Pr x y)
| Carried_by_scnd:
    forall x y z,
      carried_by z y ->
      carried_by z (Pr x y)
| Carried_by_decr:
    forall x y z,
      carried_by z x ->
      carried_by z (En x y).
#[global]
Hint Constructors carried_by : core.

Lemma carried_by_trans:
  forall x y z,
    carried_by x y ->
    carried_by y z ->
    carried_by x z.
Proof.
  intros.
  induction H0; simpl; auto.
Qed.

Lemma carried_by_reflect:
  forall x y,
    cb x y = true <-> carried_by x y.
Proof.
  split; intros.
  - functional induction (cb x y);
      try inversion H; auto; apply orb_true_iff in H;
        destruct H; try inversion H;
          try (apply alg_eq_correct in H; subst; auto).
    + apply orb_true_iff in H.
      destruct H.
      * apply IHb in H; auto.
      * apply IHb0 in H; auto.
    + apply IHb in H; auto.
  - induction H.
    + apply cb_refl.
    + destruct (alg_dec z (Pr x y)) as [G|G]; subst.
      * apply cb_refl.
      * rewrite <- alg_eq_complete in G.
        destruct x; unfold cb; rewrite G; fold cb;
          simpl in IHcarried_by; apply orb_true_iff in IHcarried_by;
            destruct IHcarried_by; try inversion IHcarried_by;
              try rewrite H0; simpl; auto; repeat rewrite orb_true_iff; auto.
    + destruct (alg_dec z (Pr x y)) as [G|G]; subst.
      * apply cb_refl.
      * rewrite <- alg_eq_complete in G.
        destruct x; unfold cb; rewrite G; fold cb; rewrite IHcarried_by;
          repeat rewrite orb_true_iff; auto.
    + destruct (alg_dec z (En x y)) as [G|G]; subst.
      * apply cb_refl.
      * rewrite <- alg_eq_complete in G.
        destruct x; unfold cb; rewrite G; fold cb;
          simpl in IHcarried_by; apply orb_true_iff in IHcarried_by;
            destruct IHcarried_by; try inversion IHcarried_by;
              try rewrite H0; simpl; auto; repeat rewrite orb_true_iff; auto.
Qed.

(** Does [x] originate in [tr]? *)

Fixpoint orig (x: alg) (tr: list evt): bool :=
  match tr with
  | nil => false
  | Sd _ y :: tr =>
    if cb x y then
      true
    else
      orig x tr
  | Rv _ y :: tr =>
    if cb x y then
      false
    else
      orig x tr
  end.

(** ** Receivable messages

A message [t] is _receivable_ iff

 - [t] contains no occurrence of an encryption in the key of an
   encryption, and
 - [t] contains no occurrence of an encryption within a hash.
*)

(** Does an encryption occur in [x]? *)

Fixpoint has_enc (x: alg): bool :=
  match x with
  | Hs y => has_enc y
  | Pr y z => has_enc y || has_enc z
  | En _ _ => true
  | _ => false
  end.

(** Is [x] receivable? *)

Fixpoint receivable (x: alg): bool :=
  match x with
  | Hs y => negb (has_enc y)
  | Pr y z => receivable y && receivable z
  | En y z => receivable y && negb (has_enc z)
  | _ => true
  end.
