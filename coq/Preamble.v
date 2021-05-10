(** * Some General Purpose Tactics *)

Require Import Bool Plus.

Ltac inv H := inversion H; clear H; subst.

Ltac find_if :=
  match goal with
  | [ |- context[ if ?X then _ else _ ] ] => destruct X
  end.

Ltac destruct_disjunct :=
  match goal with
  | [ H: _ \/ _  |- _ ] => destruct H as [H|H]
  end.

Ltac destruct_ex_and :=
  match goal with
  | [ H: _ /\ _ |- _ ] =>
    destruct H
  | [ H: exists _, _ |- _ ] =>
    destruct H
  end.

(** Expand let expressions in both the antecedent and the
    conclusion. *)

Ltac expand_let_pairs :=
  match goal with
  | |- context [let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  | [ H: context [let (_,_) := ?e in _] |- _ ] =>
    rewrite (surjective_pairing e) in H
  end.

Lemma option_dec {A} (a: option A):
  {a = None} + {exists b, a = Some b}.
Proof.
  destruct a.
  - right.
    exists a; auto.
  - left; auto.
Qed.

Ltac alt_option_dec x y H :=
  destruct (option_dec x) as [H|H];
  [ idtac | destruct H as [y H] ].

Lemma alt_bool_dec (b: bool):
  {b = true} + {b = false}.
Proof.
  destruct (bool_dec b true) as [H|H]; auto.
  rewrite not_true_iff_false in H; auto.
Qed.
