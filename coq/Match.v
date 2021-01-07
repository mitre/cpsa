(** * Matching and Role Homomorphisms *)

Require Import String Monad Alg Role.
Import List.ListNotations.
Open Scope list_scope.
(** printing <- #←# *)

(** A substitution *)

Definition sbst: Set := list (var * alg).

Definition extend_term (ev: sbst) (v: var) (x: alg): option sbst :=
  match lookup v ev with
  | None => Some ((v, x) :: ev)
  | Some y =>
    if alg_dec x y then
      Some ev
    else                        (* Term clash! *)
      None
  end.

Definition match_skey (ev: sbst) (x y: skey): option sbst :=
  match x, y with
  | Sv v, w => extend_term ev v (Sk w)
  | Lt v w, Lt x y =>
    ev <- extend_term ev v (Nm x);
    extend_term ev w (Nm y)
  | _, _ => None
  end.

Definition match_akey (ev: sbst) (x y: akey): option sbst :=
  match x, y with
  | Av v, w => extend_term ev v (Ak w)
  | Pb v, Pb w => extend_term ev v (Nm w)
  | Pb2 s v, Pb2 t w =>
    if eqb s t then
      extend_term ev v (Nm w)
    else
      None
  | _, _ => None
  end.

Fixpoint match_term (ev: sbst) (x y: alg): option sbst :=
  match x, y with
  | Tx v, Tx w => extend_term ev v (Tx w)
  | Dt v, Dt w => extend_term ev v (Dt w)
  | Nm v, Nm w => extend_term ev v (Nm w)
  | Sk v, Sk w => match_skey ev v w
  | Ak v, Ak w => match_akey ev v w
  | Ak (Av v), Ik w => extend_term ev v (Ik w)
  | Ik v, Ik w => match_akey ev v w
  | Ik (Av v), Ak w => extend_term ev v (Ik w)
  | Ch v, Ch w => extend_term ev v (Ch w)
  | Mg v, w => extend_term ev v w
  | Tg s, Tg t =>
    if eqb s t then
      Some ev
    else
      None
  | Pr v w, Pr x y =>
    ev <- match_term ev v x;
    match_term ev w y
  | En v w, En x y =>
    ev <- match_term ev v x;
    match_term ev w y
  | Hs v, Hs w => match_term ev v w
  | _, _ => None
  end.

Definition match_evt (ev: sbst) (x y: evt): option sbst :=
  match x, y with
  | Sd c x, Sd d y =>
    ev <- match_term ev (Ch c) (Ch d);
    match_term ev x y
  | Rv c x, Rv d y =>
    ev <- match_term ev (Ch c) (Ch d);
    match_term ev x y
  | _, _ => None
  end.

Fixpoint match_trace (ev: sbst) (xs ys: list evt): option sbst :=
  match xs, ys with
  | [], [] => Some ev
  | x :: xs, y :: ys =>
    ev <- match_evt ev x y;
    match_trace ev xs ys
  | _, _ => None
  end.

Fixpoint match_list (ev: sbst) (xs ys: list alg): option sbst :=
  match xs, ys with
  | [], [] => Some ev
  | x :: xs, y :: ys =>
    ev <- match_term ev x y;
    match_list ev xs ys
  | _, _ => None
end.

(** ** Role Homomorphism

    See if [x] matches one item in [ys]. *)

Fixpoint match_one (ys: list alg) (ev: sbst) (x: alg): option sbst :=
  match ys with
  | [] => None
  | y :: ys =>
    match match_term ev x y with
    | Some ev => Some ev
    | None => match_one ys ev x
    end
  end.

Definition match_uniqs (ev: sbst) (xs ys: list alg): option sbst :=
  fold_m (match_one ys) ev xs.

(** There exists a homomorphism from [x] to [y] iff the result is not
    [None]. *)

Definition homomorphism (x y: role): option sbst :=
  ev <- match_trace [] (trace x) (trace y);
  ev <- match_uniqs ev (uniqs x) (uniqs y);
  ev <- match_list ev (inputs x) (inputs y);
  match_list ev (outputs x) (outputs y).
