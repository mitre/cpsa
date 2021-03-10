(** * Role Compiler

    The role compiler translates a role specified as a [Proc.Sem.role]
    into a procedure specified as a [Proc.Proc.proc] and also returns
    the final compile time [store] produced during the compilation.

    The compiler is mostly specified by recursive functions, however,
    there is one part of the compiler that cannot be specified that
    way.  The code generated to destructure a reception is described
    by a recursive function that does not have an easily specified
    measure, and thus is not accepted by Coq.  Instead, that section
    of the code is specified by mutually inductive predicates.  This
    means code generation must be guided by a proof script. *)

Require Import List Monad Proc Alg Sem
        Unilateral_role Unilateral_proof.
Import List.ListNotations.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope program_scope.
(** printing <- #←# *)

(** A compile time store *)

Definition store: Set := list (alg * pvar).

(** Find [x] in association list [l]. *)

Fixpoint find {A} (x: alg) (l: list (alg * A)): option A :=
  match l with
  | nil => None
  | (y, v) :: l =>
    if alg_eqb x y then
      Some v
    else
      find x l
  end.

(** The state of a compilation *)

Record state: Set :=
  mkSt {
      fresh: pvar;
      cstore: store;
      code: list stmt }.

(** ** Uniques

    Function [uniq_list] computes the uniques that originate within
    each transmission in a trace.  The length of the list is the
    number of transmissions in the trace. *)

Definition uniq_here (x: alg) (u: alg) (z: list alg * list alg):
  list alg * list alg :=
  if cb u x then
    (fst z, u :: snd z)
  else
    (u :: fst z, snd z).

Fixpoint uniq_list (tr: list evt) (us: list alg): list (list alg) :=
  match tr with
  | [] => []
  | Sd _ x :: tr =>
    let (us, here) := fold_right (uniq_here x) ([], []) us in
    here :: uniq_list tr us
  | Rv _ _ :: tr => uniq_list tr us
  end.

(** Compile one unique. *)

Definition comp_uniq (st: state) (u: alg): state :=
  mkSt (S (fresh st))
       ((u, fresh st) :: cstore st)
       ((Bind (fresh st, type_of u) Nonce_) :: code st).

(** ** Trace and Outputs

    Synthesize [x] and place it in the returned variable. *)

Fixpoint synth (st: state) (x: alg): option (state * pvar) :=
  match find x (cstore st) with
  | Some v => Some (st, v)
  | None =>
    match x with
    | Tg s =>
      Some (mkSt (S (fresh st))
                 ((x, fresh st) :: cstore st)
                 ((Bind (fresh st, type_of x)
                        (Tag_ s)) :: code st),
            fresh st)
    | Pr y z =>
      l <- synth st y;;
      let (st, v) := l in
      r <- synth st z;;
      let (st, u) := r in
      Some (mkSt (S (fresh st))
                 ((x, fresh st) :: cstore st)
                 ((Bind (fresh st, type_of x)
                        (Pair_ v u)) :: code st),
            fresh st)
    | En y z =>
      l <- synth st y;;
      let (st, v) := l in
      r <- synth st z;;
      let (st, u) := r in
      Some (mkSt (S (fresh st))
                 ((x, fresh st) :: cstore st)
                 ((Bind (fresh st, type_of x)
                        (Encr_ v u)) :: code st),
            fresh st)
    | Hs y =>
      l <- synth st y;;
      let (st, v) := l in
      Some (mkSt (S (fresh st))
                 ((x, fresh st) :: cstore st)
                 ((Bind (fresh st, type_of x)
                        (Hash_ v)) :: code st),
            fresh st)
    | _ => None
    end
end.

Definition synth_fold (acc: state * list pvar) (x: alg):
  option (state * list pvar) :=
  let (st, vs) := acc in
  y <- synth st x;;
  let (st, v) := y in
  Some (st, v :: vs).

(** Synthesize procedure outputs *)

Definition synth_return (st: state) (xs: list alg):
  option (state * list pvar) :=
  w <- fold_m synth_fold (st, []) xs;;
  let (st, vs) := w in
  Some (st, rev vs).

(** *** Compile a Transmission *)

Definition comp_send (st: state) (ch: var) (x: alg)
           (us: list alg): option state :=
  let st := fold_left comp_uniq us st in
  y <- synth st x;;
  let (st, v) := y in
  z <- synth st (Ch ch);;
  let (st, u) := z in
  Some (mkSt
         (fresh st)
         (cstore st)
         (Send u v :: code st)).

(** *** Compile a Reception

    Pick some element out of a list and remove it from the list. *)

Inductive pick {A}: list A -> A -> list A -> Prop :=
| Pick_this: forall x xs,
    pick (x :: xs) x xs
| Pick_next: forall x y xs ys,
    pick xs y ys ->
    pick (x :: xs) y (x :: ys).

(** The hairy predicates for generating code to destructure a
    reception.  *)

Inductive comp_recv_loop: state -> store -> state -> Prop :=
| Comp_loop_nil: forall st, comp_recv_loop st [] st
| Comp_loop_pair: forall r x v r' st st',
    pick r (x, v) r' ->
    comp_recv_match st x v r' st' ->
    comp_recv_loop st r st'
with comp_recv_match: state -> alg -> pvar -> store ->
                      state -> Prop :=
| Comp_pair: forall st y z v r' st' st'',
    st' = mkSt
            (S (S (fresh st)))
            ((Pr y z, v) :: cstore st)
            ((Bind (S (fresh st), type_of z) (Scnd_ v))
               :: (Bind (fresh st, type_of y) (Frst_ v))
               :: code st) ->
    comp_recv_loop st' (r' ++ [(y, fresh st); (z, S (fresh st))]) st'' ->
    comp_recv_match st (Pr y z) v r' st''
| Comp_decr: forall st y z v u r' st' st'' st''',
    synth st (inv z) = Some (st', u) ->
    st'' = mkSt
            (S (fresh st'))
            ((En y z, v) :: cstore st')
            ((Bind (fresh st', type_of y)
                   (Decr_ v u)) :: code st) ->
    comp_recv_loop st'' (r' ++ [(y, fresh st)]) st''' ->
    comp_recv_match st (En y z) v r' st'''
| Comp_hash: forall st y v u r' st' st'' st''',
    synth st (Hs y) = Some (st', u) ->
    st'' = mkSt
            (fresh st')
            (cstore st')
            (Same v u :: code st) ->
    comp_recv_loop st'' r' st''' ->
    comp_recv_match st (Hs y) v r' st'''
| Comp_simple: forall st x v r' st' st'',
    is_simple x = true ->
    st' = match synth st x with
          | None =>
            mkSt
              (fresh st)
              ((x, v) :: cstore st)
              (code st)
          | Some (st'', u) =>
            mkSt
              (fresh st'')
              (cstore st'')
              (Same v u :: code st)
          end ->
    comp_recv_loop st' r' st'' ->
    comp_recv_match st x v r' st''.
#[global]
Hint Resolve Comp_loop_nil : core.

(** Add a recption and then destructure the result. *)

Inductive comp_recv (st: state) (ch: pvar) (x: alg) (st': state): Prop :=
| Comp_recv:
    comp_recv_loop (mkSt
                      (S (fresh st))
                      (cstore st)
                      ((Bind (fresh st, type_of x)
                             (Recv_ ch)) :: code st))
                   [(x, fresh st)] st' ->
    comp_recv st ch x st'.
#[global]
Hint Constructors comp_recv : core.

(** *** Compile a Trace

<<
   Parmeters:
   state:            Input state
   list evt:         Input trace
   list (list alg):  Input unique list at an event
   list alg:         Input outputs of procedure
   store:            Output store
   stmts:            Output stmts
>>
*)

Inductive comp_tr: state -> list evt -> list (list alg) ->
                   list alg -> store -> list stmt -> Prop :=
| Comp_return: forall st outs st' vs,
    synth_return st outs = Some (st', vs) ->
    comp_tr st [] [] outs (cstore st') (rev ((Return vs) :: code st'))
| Comp_sd: forall st ch x ys st' tr us outs ost ostmts,
    comp_send st ch x ys = Some st' ->
    comp_tr st' tr us outs ost ostmts ->
    comp_tr st (Sd ch x :: tr) (ys :: us) outs ost ostmts
| Comp_rv: forall st ch x st' tr us outs ost ostmts,
    comp_recv st ch x st' ->
    comp_tr st' tr us outs ost ostmts ->
    comp_tr st (Rv ch x :: tr) us outs ost ostmts.
#[global]
Hint Resolve Comp_return : core.

(** ** Inputs *)

Definition istate: Set := pvar * store * list decl.

Definition comp_input (ins: istate) (x: alg): istate :=
  let (z, decls) := ins in
  let (v, cs) := z in
  (S v, (x, v) :: cs, (v, type_of x) :: decls).

Definition comp_inputs (ins: list alg): istate :=
  fold_left comp_input ins (0, [], []).

(** *** The Role Compiler

<<
   Parmeters:
   role:     Input role
   store:    Output store
   proc:     Output procedure
>>
*)

Inductive comp (rl: role) (cs: store) (p: proc): Prop :=
| Comp: forall ist st uniques ss,
    valid_role rl = true ->
    comp_inputs (inputs rl) = ist ->
    comp_recv_loop (mkSt (fst (fst ist)) [] []) (snd (fst ist)) st  ->
    uniq_list (trace rl) (uniqs rl) = uniques ->
    comp_tr st (trace rl) uniques (outputs rl) cs ss ->
    p = mkProc (rev (snd ist)) ss ->
    comp rl cs p.

(** This predicate is used to view existential variables. *)

Ltac run_comp :=
  repeat match goal with
         | [ H: pick _ _ _ |- _ ] =>
           apply Pick_this
         | _ => econstructor; simpl; eauto
         end.

Inductive view_proc (cs: store) (p: proc): Prop :=
| View_proc: view_proc cs p.

Lemma comp_init:
    exists (cs: store) (is: list decl) (ss: list stmt),
      comp init_role cs (mkProc is ss) /\
      view_proc cs (mkProc is ss).
Proof.
  eexists; eexists; eexists; split.
  - eapply Comp; eauto; run_comp.
  - simpl.
    apply View_proc.
Qed.

Lemma comp_resp:
    exists (cs: store) (is: list decl) (ss: list stmt),
      comp resp_role cs (mkProc is ss) /\
      view_proc cs (mkProc is ss).
Proof.
  eexists; eexists; eexists; split.
  - eapply Comp; eauto; run_comp.
  - simpl.
    apply View_proc.
Qed.

(** ** Correctness Conjecture *)

Conjecture compiler_correct_liveness:
  forall (rl: role) (cs: store) (p: proc),
    comp rl cs p ->
    correct_io_liveness rl p.

Conjecture compiler_correct_safety:
  forall (rl: role) (cs: store) (p: proc),
    comp rl cs p ->
    correct_io_safety rl p.
