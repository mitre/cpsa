(** * Representation of Generated Code *)

Require Export String List.

(** A procedure variable is a nat *)

Notation pvar := nat (only parsing).

(** Sorts *)

Inductive sort: Set :=
| Text
| Data
| Name
| Skey
| Akey
| Ikey
| Mesg
| Chan.

Definition sort_dec:
  forall x y: sort, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
Defined.
Hint Resolve sort_dec : core.

(** The inverse sort *)

Definition inv_sort (x: sort): sort :=
  match x with
  | Akey => Ikey
  | Ikey => Akey
  | s => s
  end.

(** Declarations *)

Definition decl: Set := pvar * sort.

Definition decl_dec:
  forall x y: decl, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; decide equality.
Defined.
Hint Resolve decl_dec : core.

(** Expressions *)
Inductive expr: Set :=
| Tagg: string -> expr          (* Construct a tag *)
| Hash: pvar -> expr            (* Construct a hash *)
| Pair: pvar -> pvar -> expr    (* Construct a pair *)
| Encr: pvar -> pvar -> expr    (* Encrypt plain text *)
| Frst: pvar -> expr            (* Project first component of pair *)
| Scnd: pvar -> expr            (* Project second component of pair *)
| Decr: pvar -> pvar -> expr    (* Decrypt cipher text *)
| Nonce: expr                   (* Generate a nonce *)
| Recv:  pvar -> expr.          (* Receive a message *)

(** Statements *)

Inductive stmts: Set :=
| Return: list pvar -> stmts           (* Return values *)
| Bind: decl -> expr -> stmts -> stmts (* Bind a variable *)
| Send: pvar -> pvar -> stmts -> stmts (* Send a message *)
| Same: pvar -> pvar -> stmts -> stmts. (* Check for sameness *)

(** Procedures *)

Record proc: Set :=
  mkProc {
      ins: list decl;
      body: stmts }.
