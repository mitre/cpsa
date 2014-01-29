:- module(ppfile, [ppfile/2]).

:- use_module(cpsa).

ppfile(InFile, OutFile) :-
    cpsa:cpsa(InFile, Cpsas),
    cpsa:cpsas_to_sexprs(Cpsas, Sexpr),
    open(OutFile, write, Stream),
    cpsa:cpsa_sexprs_pp(Stream, Sexpr),
    close(Stream).
