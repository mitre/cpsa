(** * Representation of Generated Code *)

Require Export String List.

(** A procedure variable is a nat *)

Notation pvar := nat (only parsing).

(** Types *)

Inductive type: Set :=
| Text
| Data
| Name
| Skey
| Akey
| Ikey
| Mesg
| Quot
| Pair
| Senc
| Aenc
| Ienc
| Hash
| Chan.

Definition type_dec:
  forall x y: type, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
Defined.
#[global]
Hint Resolve type_dec : core.

Definition type_eqb x y: bool :=
  if type_dec x y then
    true
  else
    false.

Lemma type_eq_correct:
  forall x y,
    type_eqb x y = true <-> x = y.
Proof.
  intros.
  unfold type_eqb.
  destruct (type_dec x y); subst; intuition.
  inversion H.
Qed.

Lemma type_eq_complete:
  forall x y,
    type_eqb x y = false <-> x <> y.
Proof.
  intros.
  unfold type_eqb.
  destruct (type_dec x y); subst; intuition.
Qed.

(** The inverse type *)

Definition inv_type (x: type): type :=
  match x with
  | Akey => Ikey
  | Ikey => Akey
  | s => s
  end.

(** Declarations *)

Definition decl: Set := pvar * type.

Definition decl_dec:
  forall x y: decl, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
#[global]
Hint Resolve decl_dec : core.

(** Expressions *)
Inductive expr: Set :=
| Quot_: string -> expr         (* Construct a tag *)
| Hash_: pvar -> expr           (* Construct a hash *)
| Pair_: pvar -> pvar -> expr   (* Construct a pair *)
| Encr_: pvar -> pvar -> expr   (* Encrypt plain text *)
| Frst_: pvar -> expr           (* Project first component of pair *)
| Scnd_: pvar -> expr           (* Project second component of pair *)
| Decr_: pvar -> pvar -> expr   (* Decrypt cipher text *)
| Frsh_: expr                   (* Generate a nonce *)
| Recv_:  pvar -> expr.         (* Receive a message *)

(** Statements *)

Inductive stmt: Set :=
| Return: list pvar -> stmt     (* Return values *)
| Bind: decl -> expr -> stmt    (* Bind a variable *)
| Send: pvar -> pvar -> stmt    (* Send a message *)
| Same: pvar -> pvar -> stmt    (* Check for sameness *)
| Ltkp: pvar -> pvar -> pvar -> stmt (* Check Inv predicate *)
| Invp: pvar -> pvar -> stmt    (* Check Name predicate *)
| Namp: pvar -> pvar -> stmt    (* Check Name2 predicate *)
| Nm2p: pvar -> pvar -> pvar -> stmt. (* Check LTK predicate *)

(** Procedures *)

Record proc: Set :=
  mkProc {
      ins: list decl;
      body: list stmt }.
