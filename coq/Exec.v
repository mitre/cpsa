(** * Executable Roles

    Every executable role can be compiled and only executable roles
    can be compiled. *)

Require Import Proc Alg Sem Derives Comp.

(** Outputs are executable iff each one can be derived. *)

Inductive executable_outputs (pub: list alg): list alg -> Prop :=
| Exec_outs_nil: executable_outputs pub nil
| Exec_outs_pair: forall (x: alg) (xs: list alg),
    derives pub x ->
    executable_outputs pub xs ->
    executable_outputs pub (x :: xs).
#[global]
Hint Constructors executable_outputs : core.

(** Definition of reducible *)

Inductive reducible (pub: list alg) (x: alg): Prop :=
| Reducible:
    (forall y, cb y x = true -> derives pub y) ->
    (forall y z, cb (En y z) x = true -> reducible pub (inv z)) ->
    (forall y, cb (Hs y) x = true -> reducible pub y) ->
    reducible pub x.

(** Executable trace

<<
   Parmeters:
   list alg:         Outputs
   list alg:         Public messages
   list evt:         Trace
   list (list alg):  Unique list at an event
>>
*)

Inductive executable_trace
          (outs: list alg): list alg -> list evt ->
                            list (list alg) -> Prop :=
| Exec_tr_nil: forall (pub: list alg),
    executable_outputs pub outs ->
    executable_trace outs pub nil nil
| Exec_tr_sd: forall (us pub: list alg) (ch: var) (x: alg)
                     (tr: list evt) (ys: list (list alg)),
    derives (us ++ pub) (Ch ch) ->
    derives (us ++ pub) x ->
    executable_trace outs (us ++ pub) tr ys ->
    executable_trace outs pub (Sd ch x :: tr) (us :: ys)
| Exec_tr_rv: forall (pub: list alg) (ch: var) (x: alg)
                     (tr: list evt) (ys: list (list alg)),
    receivable x = true ->
    reducible (x :: pub) x ->
    derives pub (Ch ch) ->
    executable_trace outs (x :: pub) tr ys ->
    executable_trace outs pub (Rv ch x :: tr) ys.
#[global]
Hint Constructors executable_trace : core.

(** A role is executable if it is a valid execution and its trace is
    executable. *)

Definition executable (rl: role): Prop :=
  valid_role rl = true /\
  executable_trace (outputs rl) (inputs rl) (trace rl)
                   (uniq_list (trace rl) (uniqs rl)).

(** Conjectures about the how executable and comp are related. *)

Conjecture exec_implies_comp:
  forall (rl: role),
    executable rl ->
    exists (cs: store) (p: proc),
      comp rl cs p.

Conjecture comp_implies_exec:
  forall (rl: role) (cs: store) (p: proc),
    comp rl cs p ->
    executable rl.
