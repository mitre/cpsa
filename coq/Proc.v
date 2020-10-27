(** * Representation of Generated Code *)

Require Export String List.

(** A variable is a nat *)

Notation var := nat (only parsing).

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

Definition decl: Set := var * sort.

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
| Hash: var -> expr             (* Construct a hash *)
| Pair: var -> var -> expr      (* Construct a pair *)
| Encr: var -> var -> expr      (* Encrypt plain text *)
| Frst: var -> expr             (* Project first component of pair *)
| Scnd: var -> expr             (* Project second component of pair *)
| Decr: var -> var -> expr      (* Decrypt cipher text *)
| Nonce: expr                   (* Generate a nonce *)
| Recv:  var -> expr.           (* Receive a message *)

(** Statements *)

Inductive stmts: Set :=
| Return: list var -> stmts           (* Return values *)
| Bind: decl -> expr -> stmts -> stmts (* Bind a variable *)
| Send: var -> var -> stmts -> stmts  (* Send a message *)
| Same: var -> var -> stmts -> stmts. (* Check for sameness *)

(** Procedures *)

Record proc: Set :=
  mkProc {
      ins: list decl;
      body: stmts }.
