(** * Procedure Execution

    This library contains a straightforward definition of the
    semantics of procedure execution.  The semantics is specified
    using a function.  The semantics of statement execution is defined
    using a partial function that takes a runtime state and a list of
    statements and returns the final runtime environment and a list of
    terms that make up the procedure's outputs.  A runtime environment
    is a map from program variables to terms.  A runtime state contains

    - the current runtime environment,

    - the current trace, and

    - a list of the uniques that occur at the transmissions in the
      current trace. *)

Require Import Nat Bool Preamble Monad Proc Alg.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** A runtime environment *)

Definition env: Set := list (pvar * alg).

(** A runtime state *)

Record run_state: Set :=
  mkRSt {
      renv: env;
      rtr: list evt;
      runiqs: list alg }.

(** The semantics of expressions *)

Definition run_expr (rst: run_state) (ex: expr):
  option (run_state * alg) :=
  match ex with
  | Quot_ s => Some (rst, Tg s)
  | Hash_ v =>
    x <- lookup v (renv rst);;
    Some (rst, Hs x)
  | Pair_ u v =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    Some (rst, Pr x y)
  | Encr_ u v =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    Some (rst, En x y)
  | Frst_ v =>
    x <- lookup v (renv rst);;
    match x with
    | Pr y z => Some (rst, y)
    | _ => None
    end
  | Scnd_ v =>
    x <- lookup v (renv rst);;
    match x with
    | Pr y z => Some (rst, z)
    | _ => None
    end
  | Decr_ u v =>
    x <- lookup u (renv rst);;
    match x with
    | En y z =>
      k <- lookup v (renv rst);;
      if negb (has_enc k) && alg_eqb k (inv z) then
        Some (rst, y)
      else
        None
    | _ => None
    end
  | Recv_ v =>
    c <- lookup v (renv rst);;
    match rtr rst with
    | Rv d x :: tr =>
      match c with
      | Ch n =>
        if n =? d then
          Some (mkRSt (renv rst) tr (runiqs rst), x)
        else
          None
      | _ => None
      end
    | _ => None
    end
  | Frsh =>
    match runiqs rst with
    | u :: us =>
      Some (mkRSt (renv rst) (rtr rst) us, u)
    | _ => None
    end
  end.

(** Check that the type of [x] is compatible with [t]. *)

Definition type_check (x: alg) (t: type): bool :=
  type_eqb t Mesg || type_eqb (type_of x) t.

(** The semantics of statements *)

Definition run_stmt (rst: run_state) (cmd: stmt): option run_state :=
  match cmd with
  | Bind (v, t) exp =>
    sx <- run_expr rst exp;;
    let (rst, x) := sx in
    if type_check x t then
      Some (mkRSt
              ((v, x) :: renv rst)
              (rtr rst)
              (runiqs rst))
    else
      None
   | Send u v =>
     match rtr rst with
     | Sd d x :: tr =>
       c <- lookup u (renv rst);;
       match c with
       | Ch n =>
         if n =? d then
           y <- lookup v (renv rst);;
           if alg_eqb x y then
             Some (mkRSt (renv rst) tr (runiqs rst))
           else
             None
         else
           None
       | _ => None
       end
     | _ => None
    end
  | Same u v =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    if negb (has_enc x) && alg_eqb x y then
      Some rst
    else
      None
  | Ltkp u v w =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    z <- lookup w (renv rst);;
    match y, z with
    | Nm b, Nm c =>
      if alg_eqb x (Sk (Lt b c)) then
        Some rst
      else
        None
    | _, _ => None
    end
  | Invp u v =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    if negb (has_enc x) && alg_eqb x (inv y) then
      Some rst
    else
      None
  | Namp u v =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    match x, y with
    | Ak k, Nm b =>
      if akey_eqb k (Pb b) then
        Some rst
      else
        None
    | Ik k, Nm b =>
      if akey_eqb k (Pb b) then
        Some rst
      else
        None
    | _, _ => None
    end
  | Nm2p u v w =>
    x <- lookup u (renv rst);;
    y <- lookup v (renv rst);;
    z <- lookup w (renv rst);;
    match x, y, z with
    | Ak k, Tg s, Nm c =>
      if akey_eqb k (Pb2 s c) then
        Some rst
      else
        None
    | Ik k, Tg s, Nm c =>
      if akey_eqb k (Pb2 s c) then
        Some rst
      else
        None
    | _, _, _ => None
    end
  | Return _ => None
end.

(** The semantics of lists of statements *)

Fixpoint run_stmts (rst: run_state) (stmts: list stmt):
  option (env * list alg) :=
  match stmts with
  | [] => None
  | [Return vs] =>
    match rtr rst, runiqs rst with
    | [], [] =>
      xs <- map_m (fun x => lookup x (renv rst)) vs;;
      Some (renv rst, xs)
    | _, _ => None
    end
  | cmd :: stmts =>
    rst <- run_stmt rst cmd;;
    run_stmts rst stmts
  end.

(** Bind inputs with procedure parameters. *)

Fixpoint bind_inputs (ds: list decl) (xs: list alg) (renv: env):
  option env :=
  match ds, xs with
  | [], [] => Some renv
  | (v, t) :: ds, x :: xs =>
    if type_check x t then
      bind_inputs ds xs ((v, x) :: renv)
    else
      None
  | _, _ => None
  end.

(** The semantics of a procedure *)

Definition run (p: proc) (inputs: list alg) (tr: list evt) (us: list alg):
  option (env * list alg) :=
  renv <- bind_inputs (ins p) inputs [];;
  run_stmts (mkRSt (rev renv) tr us) (body p).
