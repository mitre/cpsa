(** * Derivability *)

Require Import List Alg.

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
Hint Resolve Der_tagg Der_pair Der_encr Der_hash : core.
