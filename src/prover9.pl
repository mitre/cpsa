% -*- mode: prolog -*-

%% CPSA tools in Prolog

%% Translates the output of the cpsasas program into the syntax of
%% Prover9.

%% Known to work in SWI-Prolog, but not with GNU Prolog.

%% To handle the subsort relations of the message algebra, add the
%% following axioms.

%%    all T (akey(T) -> mesg(T)).
%%    all T (skey(T) -> mesg(T)).
%%    all T (name(T) -> mesg(T)).
%%    all T (teTt(T) -> mesg(T)).
%%    all T (name(T) -> mesg(T)).

%% Copyright (c) 2011 The MITRE Corporation
%%
%% This program is free software: you can redistribute it and/or
%% modify it under the terms of the BSD License as published by the
%% University of California.

:- module(prover9, [prover9/2]).

:- use_module(pp).
:- use_module(sexpr).

%% prover9(+In, +Out) Translates cpsasas program output in file In,
%% into the syntax of Prover9 and places it in file Out.
prover9(In, Out) :-
	sexpr:read_sexpr_list(In, Forms),
	open(Out, write, Stream),
	top_forms_pp(Stream, Forms),
	close(Stream).

%% Ignore all forms except the ones that start with forall.
top_forms_pp(_, []).
top_forms_pp(Out, [[forall|Rest]|Forms]) :-
	!,
	form_to_pretty([forall|Rest], Pretty),
	pp:pr(Out, 72, Pretty),
	put_char(Out, '.'),
	nl(Out),
	nl(Out),
	top_forms_pp(Out, Forms).
top_forms_pp(Out, [_|Forms]) :-
	top_forms_pp(Out, Forms).

%% Formula classification

form_to_pretty([equal|Terms], Pretty) :-
	!,
	equal(Terms, Pretty).
form_to_pretty([implies|Forms], Pretty) :-
	!,
	implication(Forms, Pretty).
form_to_pretty([and|Forms], Pretty) :-
	!,
	junction(and, Forms, Pretty).
form_to_pretty([or| Forms], Pretty) :-
	!,
	junction(or, Forms, Pretty).
form_to_pretty([forall|Rest], Pretty) :-
	!,
	quantifier(forall, Rest, Pretty).
form_to_pretty([exists|Rest], Pretty) :-
	!,
	quantifier(exists, Rest, Pretty).
form_to_pretty(Forms, Pretty) :-
	atomic_form(Forms, Pretty).

%% In general, breaks are before binary operators.

%% Equality

equal([L, R], Pretty) :-
	term_to_pretty(L, Left),
	pp:brk(1, Brk),
	pp:atm('= ', Op),
	term_to_pretty(R, Right),
	pp:blo(0, [Left, Brk, Op, Right], Pretty).

%% Implication

implication([H, C], Pretty) :-
	form_to_pretty(H, Hypoth),
	pp:brk(1, Brk),
	pp:atm('-> ', Op),
	form_to_pretty(C, Concl),
	pp:blo(0, [Hypoth, Brk, Op, Concl], Pretty).

%% Conjunction and disjunction

junction(and, [], Pretty) :-
	pp:atm('$T', Pretty).
junction(or, [], Pretty) :-
	pp:atm('$F', Pretty).
junction(_, [Form], Pretty) :-
	!,
	form_to_pretty(Form, Pretty).
junction(Kind, [Form|Forms], Pretty) :-
	form_to_pretty(Form, First),
	junction_op(Kind, Op),
	junction_rest(Op, Forms, Pretties),
	pp:blo(0, [First|Pretties], Pretty).

junction_op(and, Pretty) :-
	pp:atm('&', Pretty).
junction_op(or, Pretty) :-
	pp:atm('|', Pretty).

junction_rest(_, [], []).
junction_rest(Op, [Form|Forms], [Brk, Op, Sp, Next|Pretties]) :-
	pp:brk(1, Brk),
	pp:atm(' ', Sp),
	form_to_pretty(Form, Next),
	junction_rest(Op, Forms, Pretties).

%% Quantifiers forall and exists

quantifier(_, [[], Body], Pretty) :-
	!,
	form_to_pretty(Body, Pretty).
quantifier(Kind, [Decls, Body], Pretty) :-
	quantifier_op(Kind, Op),
	decls(Decls, SVars),
	quantifier_preds(SVars, Vars, Preds),
	quantifier_body(Kind, Preds, Body, SBody),
	quantifier_rest(Op, Vars, SBody, Pretties),
	pp:blo(2, Pretties, Pretty).

quantifier_op(forall, Pretty) :-
	pp:atm(all, Pretty).
quantifier_op(exists, Pretty) :-
	pp:atm(exists, Pretty).

%% Collect vars in declarations.

decls(Decls, SortedVars) :-
	decls(Decls, SortedVars, []).

decls([], SVars, SVars).
decls([Decl|Decls], SVars, End) :-
	decl(Decl, _, SVars, Middle),
	decls(Decls, Middle, End).

decl([Sort], Sort, SVars, SVars) :-
	atom(Sort).
decl([Var|Decl], Sort, [(Var,Sort)|SVars], End) :-
	atom(Var),
	decl(Decl, Sort, SVars, End).

quantifier_preds([], [], []).
quantifier_preds([(Var,Sort)|SVars], [Var|Vars], [[Sort, Var]|Preds]) :-
        quantifier_preds(SVars, Vars, Preds).

quantifier_body(_, [], Body, Body) :-
        !.
quantifier_body(exists, Preds, [and|Forms], [and|Conj]) :-
        !,
        append(Preds, Forms, Conj).
quantifier_body(exists, Preds, Body, [and|Conj]) :-
        append(Preds, [Body], Conj).
quantifier_body(forall, Preds, [implies, [and|Forms], Body],
		[implies, [and|Conj], Body]) :-
        !,
        append(Preds, Forms, Conj).
quantifier_body(forall, Preds, [implies, Form, Body],
		[implies, [and|Conj], Body]) :-
        !,
        append(Preds, [Form], Conj).
quantifier_body(forall, Preds, Body, [implies, [and|Preds], Body]).

quantifier_rest(_, [], Body, [Left, Brk, Pretty, Right]) :-
	pp:atm('(', Left),
	pp:brk(0, Brk),
	form_to_pretty(Body, Pretty),
	pp:atm(')', Right).
quantifier_rest(Op, [Var|Vars], Body, [Op, Sp, V, Brk|Pretties]) :-
	pp:atm(' ', Sp),
	term_to_pretty(Var, V),
	pp:brk(1, Brk),
	quantifier_rest(Op, Vars, Body, Pretties).

% Atomic formulas

atomic_form([Pred], Pretty) :-
	atom(Pred),
	pp:atm(Pred, Pretty).
atomic_form([Pred, Term|Terms], Pretty) :-
	atom(Pred),
	pp:atm(Pred, P),
	pp:atm('(', Left),
	term_to_pretty(Term, T),
	terms_to_pretty(Terms, Ts),
	pp:blo(2, [P, Left, T|Ts], Pretty).

terms_to_pretty([], [Right]) :-
	pp:atm(')', Right).
terms_to_pretty([Term|Terms], [Comma, Brk, T|Pretties]) :-
	pp:atm(',', Comma),
	pp:brk(1, Brk),
	term_to_pretty(Term, T),
	terms_to_pretty(Terms, Pretties).

term_to_pretty(Term, Pretty) :-
	load_term(Term, Internal),
	term_pp(Internal, Pretty).

%% Load a term using CPSA's parsing rules for terms.  Also, convert
%% variables into uppercase atoms, and constants into lowercase atoms.

load_term(Term, Internal) :-
	atom(Term),
	upcase_symbol(Term, Internal).
load_term(Term, Internal) :-
	string(Term),
	string_to_atom(Term, Atom),
	downcase_symbol(Atom, Internal).
load_term(Term, Term) :-
	integer(Term),
	Term >= 0.
load_term([privk|Terms], Internals) :-
	!,
	load_term([invk, [pubk|Terms]], Internals).
load_term([cat,Term], Internals) :-
	!,
	load_term(Term, Internals).
load_term([cat,Term|Terms], [cat, X, Y]) :-
	!,
	load_term(Term, X),
	load_term([cat|Terms], Y).
load_term([enc|Terms], Internal) :-
	!,
	load_enc(Terms, Internal).
load_term([Term|Terms], [Term|Internals]) :-
	atom(Term),
	load_terms(Terms, Internals).

upcase_symbol(Atom, Symbol) :-
	atom_chars(Atom, Chars),
	upcase_parts(Chars, Parts),
	atom_chars(Symbol, Parts).

upcase_parts([First|Rest], [Lead|Tail]) :-
	upcase_atom(First, Lead),
	symbol_parts(Rest, Tail).

downcase_symbol(Atom, Symbol) :-
	atom_chars(Atom, Chars),
	downcase_parts(Chars, Parts),
	atom_chars(Symbol, Parts).

%% The null constant is used for the name of the listener role.

downcase_parts([], ['[', ']']).
downcase_parts([First|Rest], [Lead|Tail]) :-
	downcase_atom(First, Lead),
	symbol_parts(Rest, Tail).

symbol_parts([], []).
symbol_parts(['-'|Rest], ['_'|Tail]) :-
	!,
	symbol_parts(Rest, Tail).
symbol_parts([First|Rest], [First|Tail]) :-
	symbol_parts(Rest, Tail).

load_enc(Terms, [enc, X, Y]) :-
	split(Terms, As, B),
	load_term([cat|As], X),
	load_term(B, Y).

split([X], [], X).
split([X, Y|Z], [X|A], B) :-
	split([Y|Z], A, B).

load_terms([], []).
load_terms([T|Ts], [I|Is]) :-
	load_term(T, I),
	load_terms(Ts, Is).

%% Pretty print a term.

term_pp(Term, Pretty) :-
	atom(Term),
	pp:atm(Term, Pretty).
term_pp([Term], Pretty) :-
	atom(Term),
	pp:atm(Term, Pretty).
term_pp([Pred, Term|Terms], Pretty) :-
	atom(Pred),
	pp:atm(Pred, P),
	pp:atm('(', Left),
	term_pp(Term, Arg),
	args_pp(Terms, Pretties),
	blo(2, [P, Left, Arg|Pretties], Pretty).
%% Natural numbers are turned into lists of nulls.
%% The number is the length of the list.
term_pp(0, Pretty) :-
	pp:atm('[]', Pretty).
term_pp(Term, Pretty) :-
	integer(Term),
	succ(Num, Term),
	pp:atm('[[]', First),
	nat_pp(Num, Pretties),
	blo(1, [First|Pretties], Pretty).

args_pp([], [Pretty]) :-
	pp:atm(')', Pretty).
args_pp([Term|Terms], [Comma, Brk, Pretty|Pretties]) :-
	pp:atm(',', Comma),
	pp:brk(1, Brk),
	term_pp(Term, Pretty),
	args_pp(Terms, Pretties).

nat_pp(0, [Right]) :-
	!,
	pp:atm(']', Right).
nat_pp(Num, [Comma, Brk, Nil|Pretties]) :-
	succ(Num1, Num),
	pp:atm(',', Comma),
	pp:brk(1, Brk),
	pp:atm('[]', Nil),
	nat_pp(Num1, Pretties).
