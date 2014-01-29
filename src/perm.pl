% -*- mode: prolog -*-

%% Renumber strands in skeletons

%% Known to work in SWI-Prolog, but not with GNU Prolog.

%% Copyright (c) 2012 The MITRE Corporation
%%
%% This program is free software: you can redistribute it and/or
%% modify it under the terms of the BSD License as published by the
%% University of California.

:- module(perm, [cpsa_permute/3]).

:- use_module(cpsa).

%% PERMUTE STRANDS

%% A permutation of length n is represented as a list of natural
%% numbers that contains all the numbers less than n.

%% This program renumbers all the skeletons in a file that have the
%% same number of strands as is the length of the permutation.
%% Everything else is passed through unchanged.

%% For example, to swap the strands in skeletons with two strands in
%% in.txt and put the output into out.txt, type:
%%
%% perm: cpsa_permute([1,0], 'in.txt', 'out.txt').

%% This program does not check that the given permutation is in fact a
%% valid permutation, so be sure to check your output carefully.

cpsa_permute(Perm, InFile, OutFile) :-
    cpsa:cpsa(InFile, Cpsas),
    cpsa_permute_all(Perm, Cpsas, OutCpsas),
    cpsa:cpsas_to_sexprs(OutCpsas, Sexpr),
    open(OutFile, write, Stream),
    cpsa:cpsa_sexprs_pp(Stream, Sexpr),
    close(Stream).

cpsa_permute_all(_, [], []).
cpsa_permute_all(Perm, [Cpsa|Cpsas], [OutCpsa|OutCpsas]) :-
    cpsa_permute_skel(Perm, Cpsa, OutCpsa),
    cpsa_permute_all(Perm, Cpsas, OutCpsas).

cpsa_permute_skel(Perm, k(Prot, Decls, Strands, Precedes, Nons, Pens, Uniqs),
		  k(Prot, Decls, OutStrands, OutPrecedes, Nons, Pens, Uniqs)) :-
    perm_list(Perm, Strands, OutStrands),
    perm_precedes(Perm, Precedes, OutPrecedes),
    !.
% If above fails, simply copy the input to the output and don't fail.
cpsa_permute_skel(_, Cpsa, Cpsa).

%% Apply a permutation to a list.
perm_list([], _, []).
perm_list([Index|Indices], List, [Value|Rest]) :-
    nth0(Index, List, Value),
    perm_list(Indices, List, Rest).

%% Apply a permutation to a list of pairs of nodes.
perm_precedes(_, [], []).
perm_precedes(Perm, [(N0, N1)|Precedes], [(OutN0, OutN1)|OutPrecedes]) :-
    perm_node(Perm, N0, OutN0),
    perm_node(Perm, N1, OutN1),
    perm_precedes(Perm, Precedes, OutPrecedes).

perm_node(Perm, (S, I), (OutS, I)) :-
    index_of(Perm, S, OutS).

% Returns the index of the first occurence of Element in List
index_of(List, Element, Index) :-
    index_of(List, Element, 0, Index).
index_of([],_,_,_) :-
    print_message(error,'Element not found in list'),
    fail.
index_of([Element|_], Element, Curr, Curr) :- !.
index_of([_|List], Element, Curr, Index) :-
    Next is Curr + 1,
    index_of(List, Element, Next, Index).
