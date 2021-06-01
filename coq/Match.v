(** * Matching

    A term [x] matches [y] if there is a substitution [sb] such that
    applying [sb] to [x] gives [y].  The match function defined within
    computes substitutions. *)

Require Import String Monad Alg Role.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** A substitution *)

Definition sbst: Set := list (var * alg).

Definition extend_term (sb: sbst) (v: var) (x: alg): option sbst :=
  match lookup v sb with
  | None => Some ((v, x) :: sb)
  | Some y =>
    if alg_dec x y then
      Some sb
    else                        (* Term clash! *)
      None
  end.

Definition match_skey (sb: sbst) (x y: skey): option sbst :=
  match x, y with
  | Sv v, w => extend_term sb v (Sk w)
  | Lt v w, Lt x y =>
    sb <- extend_term sb v (Nm x);;
    extend_term sb w (Nm y)
  | _, _ => None
  end.

Definition match_akey (sb: sbst) (x y: akey): option sbst :=
  match x, y with
  | Av v, w => extend_term sb v (Ak w)
  | Pb v, Pb w => extend_term sb v (Nm w)
  | Pb2 s v, Pb2 t w =>
    if eqb s t then
      extend_term sb v (Nm w)
    else
      None
  | _, _ => None
  end.

(** Definition of matching *)

Fixpoint match_term (sb: sbst) (x y: alg): option sbst :=
  match x, y with
  | Tx v, Tx w => extend_term sb v (Tx w)
  | Dt v, Dt w => extend_term sb v (Dt w)
  | Nm v, Nm w => extend_term sb v (Nm w)
  | Sk v, Sk w => match_skey sb v w
  | Ak v, Ak w => match_akey sb v w
  | Ak (Av v), Ik w => extend_term sb v (Ik w)
  | Ik v, Ik w => match_akey sb v w
  | Ik (Av v), Ak w => extend_term sb v (Ik w)
  | Ch v, Ch w => extend_term sb v (Ch w)
  | Mg v, w => extend_term sb v w
  | Tg s, Tg t =>
    if eqb s t then
      Some sb
    else
      None
  | Pr v w, Pr x y =>
    sb <- match_term sb v x;;
    match_term sb w y
  | En v w, En x y =>
    sb <- match_term sb v x;;
    match_term sb w y
  | Hs v, Hs w => match_term sb v w
  | _, _ => None
  end.

(** ** Role Homomorphism

    See if [x] matches one item in [ys]. *)

Definition match_evt (sb: sbst) (x y: evt): option sbst :=
  match x, y with
  | Sd c x, Sd d y =>
    sb <- match_term sb (Ch c) (Ch d);;
    match_term sb x y
  | Rv c x, Rv d y =>
    sb <- match_term sb (Ch c) (Ch d);;
    match_term sb x y
  | _, _ => None
  end.

Fixpoint match_trace (sb: sbst) (xs ys: list evt): option sbst :=
  match xs, ys with
  | [], [] => Some sb
  | x :: xs, y :: ys =>
    sb <- match_evt sb x y;;
    match_trace sb xs ys
  | _, _ => None
  end.

Fixpoint match_list (sb: sbst) (xs ys: list alg): option sbst :=
  match xs, ys with
  | [], [] => Some sb
  | x :: xs, y :: ys =>
    sb <- match_term sb x y;;
    match_list sb xs ys
  | _, _ => None
end.

Fixpoint match_one (ys: list alg) (sb: sbst) (x: alg): option sbst :=
  match ys with
  | [] => None
  | y :: ys =>
    match match_term sb x y with
    | Some sb => Some sb
    | None => match_one ys sb x
    end
  end.

Definition match_uniqs (sb: sbst) (xs ys: list alg): option sbst :=
  fold_m (match_one ys) sb xs.

(** There exists a homomorphism from [x] to [y] iff the result is not
    [None]. *)

Definition homomorphism (x y: role): option sbst :=
  sb <- match_trace [] (trace x) (trace y);;
  sb <- match_uniqs sb (uniqs x) (uniqs y);;
  sb <- match_list sb (inputs x) (inputs y);;
  match_list sb (outputs x) (outputs y).
