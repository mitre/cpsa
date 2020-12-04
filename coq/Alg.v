(** * The Message Algebra *)

Require Import Nat DecBool Monad Proc.
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
Hint Resolve akey_dec : core.

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
Hint Resolve alg_dec : core.

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
Hint Resolve evt_dec : core.

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

(** ** Sort of an Algebra Term *)

Definition sort_of (x: alg): sort :=
  match x with
  | Tx v => Text
  | Dt v => Data
  | Nm v => Name
  | Sk k => Skey
  | Ak k => Akey
  | Ik k => Ikey
  | Ch v => Chan
  | _ => Mesg
  end.

(** ** Is a Term Well Formed?

    When a term is well formed, variables must have a consistent sort.
    An example of a term that is not well formed is
<<
    Pr (Tx 0) (Nm 0)
>>
    The sort of variable 0 can't be both [Text] and [Name].
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

Definition extend decls (v: var) (s: sort): option (list decl) :=
  match lookup v decls with
  | None => Some ((v, s) :: decls)
  | Some s' =>
    if sort_dec s' s then
      Some decls
    else                        (* Sort clash! *)
      None
  end.

(** Is skey well formed? *)

Definition well_formed_skey decls (k: skey): option (list decl) :=
  match k with
  | Sv v => extend decls v Skey
  | Lt v v' =>
    ds <- extend decls v Name;
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
    ds <- well_formed decls y;
    well_formed ds z
  | En y z =>
    ds <- well_formed decls y;
    well_formed ds z
  | Hs y => well_formed decls y
  end.

Definition well_formed_event decls (x: evt): option (list decl) :=
  match x with
  | Sd ch y =>
    ds <- extend decls ch Chan;
    well_formed ds y
  | Rv ch y =>
    ds <- extend decls ch Chan;
    well_formed ds y
  end.

(** ** Is a Term Well Sorted?

    Like well formed except it does not extend its declarations. *)

Definition well_sorted_var decls (v: var) (s: sort): bool :=
  match lookup v decls with
  | None => false
  | Some s' => ifdec (sort_dec s' s) true false
  end.

(** Is skey well sorted? *)

Definition well_sorted_skey decls (k: skey): bool :=
  match k with
  | Sv v => well_sorted_var decls v Skey
  | Lt v v' => well_sorted_var decls v Name &&
               well_sorted_var decls v' Name
  end.

(** Is akey well sorted? *)

Definition well_sorted_akey decls (k: akey): bool :=
  match k with
  | Av v => well_sorted_var decls v Akey
  | Pb v =>  well_sorted_var decls v Name
  | Pb2 c v =>  well_sorted_var decls v Name
  end.

(** Is algebra term well sorted?  For term [x], [well_sorted decl x]
    is true when [x] is true when it is well sorted with respect to
    the declarations [decls].  Note that channels are considered not
    well sorted in this function. *)

Fixpoint well_sorted decls (x: alg): bool :=
  match x with
  | Tx v => well_sorted_var decls v Text
  | Dt v => well_sorted_var decls v Data
  | Nm v => well_sorted_var decls v Name
  | Sk k => well_sorted_skey decls k
  | Ak k => well_sorted_akey decls k
  | Ik k => well_sorted_akey decls k
  | Ch v => false               (* Channels are forbidden *)
  | Mg v => well_sorted_var decls v Mesg
  | Tg z => true
  | Pr y z => well_sorted decls y &&
              well_sorted decls z
  | En y z => well_sorted decls y &&
              well_sorted decls z
  | Hs y => well_sorted decls y
  end.

(** Is algebra term or channel well sorted? *)

Definition well_sorted_with_chan decls (x: alg): bool :=
  match x with
  | Ch v => well_sorted_var decls v Chan
  | _ => well_sorted decls x
  end.

(** ** Measure of a term *)

Fixpoint size (x: alg): nat :=
  match x with
  | Pr y z => S (size y + size z)
  | En y z => S (size y + size z)
  | Hs y => S (size y)
  | _ => 0
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
  if alg_dec x y then
    true
  else
    match y with
    | Pr a b => cb x a || cb x b
    | En a _ => cb x a
    | _ => false
    end.

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
