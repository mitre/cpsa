filenametemplate "%j-%c.mps";

verbatimtex
\documentclass[12pt]{article}
\newcommand{\enc}[2]{\{\!|#1|\!\}_{#2}}
\begin{document}
etex

input boxes;

pair w; w = (4in, 0);		% Width of diagram

alpha = .45;			% Row offset ratio for messages
beta = .85;		        % Row offset ratio for shortened arrows

input strands;

input cmstrands;		% Use CM arrows

picture node; node = btex $\bullet$ etex;

% The height of a downarrow is the unit of length for a strand
% succession edge.

numeric delta;
begingroup;
  path p; p = bbox(btex $\downarrow$ etex);
  delta = ypart(ulcorner p - llcorner p);
endgroup;

% The width of a leftarrow is the unit of length for a directed term
% symbol.

numeric dir_width;
begingroup;
  path p; p = bbox(btex $\leftarrow$ etex);
  dir_width = xpart (lrcorner p - llcorner p);
endgroup;

% Needham-Schroeder Protocol

% Initiator role

beginfig(0);
  % Backbone
  strand.a(3, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Messages
  outbnd.a(1, dir_width, btex $\enc{N_1, A}{K_B}$ etex);
  inbnd.a(2, dir_width, btex $\enc{N_1, N_2}{K_A}$ etex);
  outbnd.a(3, dir_width, btex $\enc{N_2}{K_B}$ etex);
endfig;

% Responder role

beginfig(1);
  % Backbone
  strand.a(3, origin, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages
  rinbnd.a(1, dir_width, btex $\enc{N_1, A}{K_B}$ etex);
  routbnd.a(2, dir_width, btex $\enc{N_1, N_2}{K_A}$ etex);
  rinbnd.a(3, dir_width, btex $\enc{N_2}{K_B}$ etex);
endfig;

% Intended run

beginfig(2);
  % Strand for principal A
  strand.a(3, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Strand for principal B
  strand.b(3, .5w, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages and arrows
  label.top(btex $\enc{N_1, A}{K_B}$ etex, .5[a1.e, b1.w]);
  drawmsg(a1.e -- b1.w);
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, .5[a2.e, b2.w]);
  drawmsg(b2.w -- a2.e);
  label.top(btex $\enc{N_2}{K_B}$ etex, .5[a3.e, b3.w]);
  drawmsg(a3.e -- b3.w);
endfig;

% Penetrated run

beginfig(3);
  % Strand for principal B
  boxstrand.b(3, w, btex $\mathstrut B$ etex, node);
  draw pic b3;

  % Strand for principal P
  boxstrand.p(4, .5w, btex $\mathstrut P$ etex, node);
  draw pic p4;

  spacestrand.p(3, delta);
  draw pic p3;

  % Strand for principal A
  boxstrand.a(3, p3.c - p4.c, btex $\mathstrut A$ etex, node);
  draw pic a3;

  spacestrand.a(2, delta);
  draw pic a2;

  ypart b2.c = ypart a2.c;
  draw pic b2;

  spacestrand.b(1, delta);
  draw pic b1;

  ypart p2.c = ypart b1.c;
  draw pic p2;

  spacestrand.p(1, delta);
  draw pic p1;

  ypart a1.c = ypart p1.c;
  draw pic a1;

  drawsucc(a1.s -- a2.n);
  drawsucc(a2.s -- a3.n);
  drawsucc(p1.s -- p2.n);
  drawsucc(p2.s -- p3.n);
  drawsucc(p3.s -- p4.n);
  drawsucc(b1.s -- b2.n);
  drawsucc(b2.s -- b3.n);

  label.top(btex $\enc{N_1, A}{K_P}$ etex, .5[a1.e, p1.w]);
  drawmsg(a1.e -- p1.w);
  label.top(btex $\enc{N_1, A}{K_B}$ etex, .5[p2.e, b1.w]);
  drawmsg(p2.e -- b1.w);
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, .75[b2.w, a2.e]);
  drawmsg(b2.w -- a2.e);
  label.top(btex $\enc{N_2}{K_P}$ etex, .5[a3.e, p3.w]);
  drawmsg(a3.e -- p3.w);
  label.top(btex $\enc{N_2}{K_B}$ etex, .5[p4.e, b3.w]);
  drawmsg(p4.e -- b3.w);
endfig;

% Shape with $K^{-1}_A$ uncompromised, $N_2$ fresh

beginfig(4);
  % Strand for principal A
  strand.a(3, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Strand for principal B
  strand.b(3, w, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Centered ordering symbols
  boxit.o1(btex \phantom{$\prec$} etex); o1.c = .5[a1.c, b1.c];
  boxit.o2(btex $\succ$ etex); o2.c = .5[a2.c, b2.c];
  boxit.o3(btex $\prec$ etex); o3.c = .5[a3.c, b3.c];

  for i = 1 upto 3:
    draw pic o[i];
  endfor;

  % Messages and arrows
  label.top(btex $\enc{N_1, A}{K_C}$ etex, alpha[a1.e, o1.w]);
  drawmsg(a1.e -- beta[a1.e,o1.w]); % Shortened arrow
  label.top(btex $\enc{N_1, A}{K_B}$ etex, alpha[b1.w, o1.e]);
  drawmsg(beta[b1.w,o1.e] -- b1.w); % Shortened arrow
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, alpha[a2.e, o2.w]);
  drawmsg(o2.w -- a2.e);
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, alpha[b2.w, o2.e]);
  drawmsg(b2.w -- o2.e);
  label.top(btex $\enc{N_2}{K_C}$ etex, alpha[a3.e, o3.w]);
  drawmsg(a3.e -- o3.w);
  label.top(btex $\enc{N_2}{K_B}$ etex, alpha[b3.w, o3.e]);
  drawmsg(o3.e -- b3.w);
endfig;

beginfig(5);
  % Strand for principal A
  strand.a(3, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Strand for principal B
  strand.b(2, w + a2.c, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Centered ordering symbols
  boxit.o1(btex $\prec$ etex); o1.c = .5[a1.c, b1.c];
  boxit.o2(btex $\succ$ etex); o2.c = .5[a2.c, b2.c];

  for i = 1 upto 2:
    draw pic o[i];
  endfor;

  % Messages and arrows
  label.top(btex $\enc{N_1, A}{K_B}$ etex, alpha[a1.e, o1.w]);
  drawmsg(a1.e -- o1.w);
  label.top(btex $\enc{N_1, A}{K_B}$ etex, alpha[b1.w, o1.e]);
  drawmsg(o1.e -- b1.w);
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, alpha[a2.e, o2.w]);
  drawmsg(o2.w -- a2.e);
  label.top(btex $\enc{N_1, N_2}{K_A}$ etex, alpha[b2.w, o2.e]);
  drawmsg(b2.w -- o2.e);
  label.top(btex $\enc{N_2}{K_B}$ etex,
    alpha[a3.e, (xpart o2.w, ypart a3.c)]);
  drawmsg(a3.e -- (beta * xpart o2.w, ypart a3.c));
endfig;

% Incompleteness example

% Initiator role

beginfig(6);
  % Backbone
  strand.a(2, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Messages
  outbnd.a(1, dir_width, btex $\enc{N}{K}$ etex);
  inbnd.a(2, dir_width, btex $N$ etex);
endfig;

% Responder role

beginfig(7);
  % Backbone
  strand.a(2, origin, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages
  rinbnd.a(1, dir_width, btex $\enc{N_1}{K}$ etex);
  routbnd.a(2, dir_width, btex $N_2$ etex);
endfig;

% Omitted run

beginfig(8);
  % Strand for principal A
  strand.a(2, origin, delta, btex $\mathstrut\mathit{init}$ etex, node);

  % Strand for principal B
  strand.b(2, .5w, delta, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages and arrows
  label.top(btex $\enc{N}{K}$ etex, .5[a1.e, b1.w]);
  drawmsg(a1.e -- b1.w);
  label.top(btex $N$ etex, .5[a2.e, b2.w]);
  drawmsg(b2.w -- a2.e);
endfig;

verbatimtex
\end{document}
etex
bye;
