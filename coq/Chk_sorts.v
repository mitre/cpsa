(** * Example of Functional Induction *)

Require Import FunInd Proc Alg.

Fixpoint chk_sorts (ds: list decl) (xs: list alg): bool :=
  match (ds, xs) with
  | (nil, nil) => true
  | ((_, s) :: ds, x :: xs) =>
    if sort_dec s (sort_of x) then
      chk_sorts ds xs
    else
      false
  | _ => false
  end.

Functional Scheme chk_sorts_ind :=
  Induction for chk_sorts Sort Prop.

(** Checked sorts is [true] implies its inputs have the same
    length. *)

Lemma chk_sorts_length:
  forall ds xs,
    chk_sorts ds xs = true ->
    length ds = length xs.
Proof.
  intros.
  functional induction (chk_sorts ds xs);
    simpl; auto; inversion H.
Qed.
