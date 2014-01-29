% -*- mode: prolog -*-

%% Unsorted CPSA terms

%% Copyright (c) 2013 The MITRE Corporation
%%
%% This program is free software: you can redistribute it and/or
%% modify it under the terms of the BSD License as published by the
%% University of California.

:- module(unsorted, [to_unsorted/3, from_unsorted/3,
                     unify/3, unify/4, subst/3]).

:- use_module(cpsa).

%% An unsorted term has inclusion operations inserted to preserve sort
%% constraints within an unsorted algebra.  It also replaces the privk
%% operation in favor of invk o pubk.

%% Term ::= Tag | Var | name(Var) | text(Var) | data(Var) | akey(Akey)
%%       |  skey(Skey) | cat(Term, Term) | enc(Term, Term) | hash(Term).
%% Akey ::= Var | invk(Akey) | pubk(Var) | pubk(Tag, Var).
%% Skey ::= Var | ltk(Var, Var).

%% to_unsorted(+Decls, +Term, -Uterm)
to_unsorted(Decls, Term, Uterm) :-
    % Add inclusion operation to each variable that needs one
    decls_as_pairs(Decls, VarMap),
    to_unsorted_term(VarMap, Term, Uterm).

% Note that the operation privk is eliminated in favor of invk o pubk.
to_unsorted_term(_, Term, Term) :-
    string(Term),		% Case of tags
    !.
to_unsorted_term(VarMap, Term, Uterm) :-
    atom(Term),			% Case of variables
    lookup(Term, VarMap, Uterm).
to_unsorted_term(VarMap, invk(Term), akey(invk(Uterm))) :-
    to_unsorted_term(VarMap, Term, akey(Uterm)).
to_unsorted_term(VarMap, pubk(Term), akey(pubk(Uterm))) :-
    to_unsorted_term(VarMap, Term, name(Uterm)).
to_unsorted_term(VarMap, pubk(Term0, Term1), akey(pubk(Uterm0, Uterm1))) :-
    string(Uterm0),		% Case of pubk(tag, name var)
    to_unsorted_term(VarMap, Term0, Uterm0),
    to_unsorted_term(VarMap, Term1, name(Uterm1)).
to_unsorted_term(VarMap, privk(Term), Uterm) :-
    to_unsorted_term(VarMap, invk(pubk(Term)), Uterm).
to_unsorted_term(VarMap, privk(Term0, Term1), Uterm) :-
    to_unsorted_term(VarMap, invk(pubk(Term0, Term1)), Uterm).
to_unsorted_term(VarMap, ltk(Term0, Term1), skey(ltk(Uterm0, Uterm1))) :-
    to_unsorted_term(VarMap, Term0, name(Uterm0)),
    to_unsorted_term(VarMap, Term1, name(Uterm1)).
to_unsorted_term(VarMap, cat(Term0, Term1), cat(Uterm0, Uterm1)) :-
    to_unsorted_term(VarMap, Term0, Uterm0),
    to_unsorted_term(VarMap, Term1, Uterm1).
to_unsorted_term(VarMap, enc(Term0, Term1), enc(Uterm0, Uterm1)) :-
    to_unsorted_term(VarMap, Term0, Uterm0),
    to_unsorted_term(VarMap, Term1, Uterm1).
to_unsorted_term(VarMap, hash(Term), hash(Uterm)) :-
    to_unsorted_term(VarMap, Term, Uterm).

% Adds inclusion operations to variables other than those of sort mesg.
decls_as_pairs([], []).
decls_as_pairs([d(Sort, Vars)|Decls], VarMap) :-
    decl_as_pairs(Vars, Sort, Decls, VarMap).

decl_as_pairs([], _, Decls, VarMap) :-
    decls_as_pairs(Decls, VarMap).
decl_as_pairs(_, mesg, Decls, VarMap) :-
    !,
    decls_as_pairs(Decls, VarMap).
decl_as_pairs([Var|Vars], Sort, Decls, [(Var, Term)|VarMap]) :-
    Term =.. [Sort, Var],
    decl_as_pairs(Vars, Sort, Decls, VarMap).

% Lookup value in an association list
lookup(Key, [(Key, Value)|_], Value) :-
    !.
lookup(Key, [_|Map], Value) :-
    lookup(Key, Map, Value).

% From unsorted translates back to the order-sorted algebra
% representation and also produces the appropriate variable
% declaration.

%% from_unsorted(+Uterm, -Term, -Decls).
from_unsorted(InTerm, OutTerm, Decls) :-
    from_unsorted_term(InTerm, [], OutTerm, Map),
    pairs_as_decls(Map, [], Decls).

% Convert an association list representation to a list of declarations.
pairs_as_decls([], Decls, Decls).
% Case when sort decls has already been constructed
pairs_as_decls([(_, Value)|Map], Decls, Decls) :-
    member(d(Value, _), Decls),
    !,
    pairs_as_decls(Map, Decls, Decls).
% Construct one sort decl
pairs_as_decls([(Var, Value)|Map], Decls, [d(Value, [Var|Vars])|Decls]) :-
    select(Value, Map, Vars).

% Collect vars of a given sort.
select(_, [], []).
select(Value, [(Var, Value)|Map], [Var|Vars]) :-
    !,
    select(Value, Map, Vars).
select(Value, [_|Map], Vars) :-
    select(Value, Map, Vars).

%% The core of the translation is here.

%% from_unsorted_term(+InTerm, +InMap, -OutTerm, -OutMap).
from_unsorted_term(Term, Map, Term, Map) :-
    string(Term),		% Tags
    !.
from_unsorted_term(Term, InMap, Term, OutMap) :-
    atom(Term),			% Variables of sort mesg
    extend_map(Term, mesg, InMap, OutMap).
from_unsorted_term(name(Term), InMap, Term, OutMap) :-
    atom(Term),			% Variables of sort name
    extend_map(Term, name, InMap, OutMap).
from_unsorted_term(text(Term), InMap, Term, OutMap) :-
    atom(Term),			% Variables of sort text
    extend_map(Term, text, InMap, OutMap).
from_unsorted_term(data(Term), InMap, Term, OutMap) :-
    atom(Term),			% Variables of sort data
    extend_map(Term, data, InMap, OutMap).
from_unsorted_term(skey(InTerm), InMap, OutTerm, OutMap) :-
    from_unsorted_skey_term(InTerm, InMap, OutTerm, OutMap).
from_unsorted_term(akey(InTerm), InMap, OutTerm, OutMap) :-
    from_unsorted_akey_term(InTerm, InMap, OutTerm, OutMap).
from_unsorted_term(cat(InTerm0, InTerm1), InMap, % Pairs
		   cat(OutTerm0, OutTerm1), OutMap) :-
    from_unsorted_term(InTerm0, InMap, OutTerm0, Map),
    from_unsorted_term(InTerm1, Map, OutTerm1, OutMap).
from_unsorted_term(enc(InTerm0, InTerm1), InMap, % Encryption
		   enc(OutTerm0, OutTerm1), OutMap) :-
    from_unsorted_term(InTerm0, InMap, OutTerm0, Map),
    from_unsorted_term(InTerm1, Map, OutTerm1, OutMap).

% Terms of sort skey
from_unsorted_skey_term(Term, InMap, Term, OutMap) :-
    atom(Term), 		% Variables of sort skey
    extend_map(Term, skey, InMap, OutMap).
% ltk: long term keys
from_unsorted_skey_term(ltk(InTerm0, InTerm1), InMap,
			ltk(OutTerm0, OutTerm1), OutMap) :-
    from_unsorted_term(name(InTerm0), InMap, OutTerm0, Map),
    from_unsorted_term(name(InTerm1), Map, OutTerm1, OutMap).

% Terms of sort akey
from_unsorted_akey_term(Term, InMap, Term, OutMap) :-
    atom(Term), 		% Variables of sort akey
    extend_map(Term, akey, InMap, OutMap).
from_unsorted_akey_term(invk(pubk(InTerm)), InMap, privk(OutTerm), OutMap) :-
    !,				% privk
    from_unsorted_term(name(InTerm), InMap, OutTerm, OutMap).
from_unsorted_akey_term(pubk(InTerm), InMap, pubk(OutTerm), OutMap) :-
    from_unsorted_term(name(InTerm), InMap, OutTerm, OutMap). % pubk
from_unsorted_akey_term(invk(InTerm), InMap, invk(OutTerm), OutMap) :-
    from_unsorted_akey_term(InTerm, InMap, OutTerm, OutMap). % invk

% Extend a mapping or fail with an inconsistent mapping.
%% extend_map(+Key, +Value, +Map, -NewMap).
extend_map(Key, Value, Map, Map) :-
    lookup(Key, Map, Result),
    !,
    Result = Value.	   % Fails when key is mapped to another value
% Extend Map when Key is not mapped as long as var does occur in term
extend_map(Key, Value, Map, [(Key, Value)|Map]) :-
    \+occurs(Key, Value).

occurs(Var, Var).
occurs(Var, Term) :-
    Term =.. [_|Terms],
    occurs_list(Var, Terms).

occurs_list(Var, [Term|_]) :-
    occurs(Var, Term),
    !.
occurs_list(Var, [_|Terms]) :-
    occurs_list(Var, Terms).

%% Unification of unsorted terms given the equation invk(invk(k)) = k.

%% unify(+Term0, +Term1, -Subst).
unify(Term0, Term1, Subst) :-
    unify(Term0, Term1, [], Subst).

%% This version extends a substition.
%% unify(+Term0, +Term1, +InSubst, -OutSubst).
unify(Term0, Term1, InSubst, OutSubst) :-
    chase(Term0, InSubst, Term2),
    chase(Term1, InSubst, Term3),
    unify_aux(Term2, Term3, InSubst, OutSubst).

%% Find the canonical variable within an equivalence class.
%% This version of the chase handles the equation invk(invk(k)) = k.
chase(Term, _, Term) :-
    string(Term),		% Tag
    !.
chase(InTerm, Subst, OutTerm) :-
    atom(InTerm),		% Variable
    !,
    chase_var(InTerm, Subst, OutTerm).
chase(invk(InTerm), Subst, OutTerm) :-
    !,
    chase_invk(InTerm, Subst, OutTerm).
chase(Term, _, Term).

chase_var(InTerm, Subst, OutTerm) :-
    lookup(InTerm, Subst, Term),
    !,
    chase(Term, Subst, OutTerm).
chase_var(Term, _, Term).

chase_invk(Term, _, Term) :-
    string(Term),		% This should never happen
    !.
chase_invk(InTerm, Subst, OutTerm) :-
    atom(InTerm),
    !,
    chase_invk_var(InTerm, Subst, OutTerm).
chase_invk(invk(InTerm), Subst, OutTerm) :-
    !,
    chase(InTerm, Subst, OutTerm).
chase_invk(Term, _, invk(Term)).

chase_invk_var(InTerm, Subst, OutTerm) :-
    lookup(InTerm, Subst, Term),
    !,
    chase_invk(Term, Subst, OutTerm).
chase_invk_var(Term, _, invk(Term)).

%% The remainder of unification assumes that the chase has been
%% applied to the two terms.

unify_aux(Term, Term, Subst, Subst).
unify_aux(Term0, _, Subst, Subst) :-
    string(Term0),
    !,
    fail.
unify_aux(Term0, Term1, InSubst, OutSubst) :-
    atom(Term0),
    !,
    extend_map(Term0, Term1, InSubst, OutSubst).
unify_aux(Term0, Term1, InSubst, OutSubst) :-
    atom(Term1),
    !,
    unify_aux(Term1, Term0, InSubst, OutSubst).
%% Clauses that handle the equation
unify_aux(invk(Term0), pubk(Term1), InSubst, OutSubst) :-
    unify_aux(Term0, invk(pubk(Term1)), InSubst, OutSubst).
unify_aux(pubk(Term0), invk(Term1), InSubst, OutSubst) :-
    unify_aux(Term1, invk(pubk(Term0)), InSubst, OutSubst).
%% Clause that handles other function symbols
unify_aux(Term0, Term1, InSubst, OutSubst) :-
    Term0 =.. [Fun|Terms0],
    Term1 =.. [Fun|Terms1],
    unify_list(Terms0, Terms1, InSubst, OutSubst).

unify_list([], [], Subst, Subst).
unify_list([Term0|Terms0], [Term1|Terms1], InSubst, OutSubst) :-
    unify(Term0, Term1, InSubst, Subst),
    unify_list(Terms0, Terms1, Subst, OutSubst).

%% Substition

%% subst(+InTerm, +Subst, -OutTerm).

subst(InTerm, Subst, OutTerm) :-
    chase(InTerm, Subst, Term),
    subst_aux(Term, Subst, OutTerm).

subst_aux(Term, _, Term) :-
    atom(Term),
    !.
subst_aux(Term, _, Term) :-
    string(Term),
    !.
% Apply equation
subst_aux(invk(InTerm), Subst, OutTerm) :-
    subst(InTerm, Subst, invk(OutTerm)),
    !.
subst_aux(InTerm, Subst, OutTerm) :-
    InTerm =.. [Fun|InTerms],
    subst_list(InTerms, Subst, OutTerms),
    OutTerm =.. [Fun|OutTerms].

subst_list([], _, []).
subst_list([InTerm|InTerms], Subst, [OutTerm|OutTerms]) :-
    subst(InTerm, Subst, OutTerm),
    subst_list(InTerms, Subst, OutTerms).
