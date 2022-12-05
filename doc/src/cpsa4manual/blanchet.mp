filenametemplate "%j-%c.mps";

verbatimtex
\documentclass{slides}
\usepackage{color}
\newcommand{\enc}[2]{\{\!|#1|\!\}_{#2}}
\newcommand{\privk}[1]{\ensuremath{K^{-1}_{#1}}}
\newcommand{\pubk}[1]{\ensuremath{K_{#1}}}
\newcommand{\msgone}{$\enc{\enc{S}{\privk{A}}}{\pubk{B}}$}
\newcommand{\msgtwo}{$\enc{D}{S}$}
\newcommand{\msgthree}{$\enc{\enc{S,B}{\privk{A}}}{\pubk{B}}$}
\newcommand{\msgfour}{$\enc{\enc{S}{\privk{A}}}{\pubk{\textcolor{blue}{B'}}}$}
\newcommand{\msgfive}{$\enc{\enc{S}{\privk{A}}}{\pubk{B'}}$}
\newcommand{\msgsix}{\ensuremath{\enc{S}{\privk{A}}}}
\begin{document}
etex

input boxes;

input strands;

input cmstrands;

ahlength := 2mm;		% Arrow head length

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

w = 19cm;			% Width of diagram

% Node vertical node separation is gamma

numeric gamma;
gamma = 2delta;

beginfig(0);
  % Backbone
  strand.a(2, origin, gamma, btex $\mathstrut\mathit{init}$ etex, node);

  % Messages
  outbnd.a(1, dir_width, btex \msgone etex);
  inbnd.a(2, dir_width, btex \msgtwo etex);
endfig;

% Responder role

beginfig(1);
  % Backbone
  strand.a(2, origin, gamma, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages
  rinbnd.a(1, dir_width, btex \msgone etex);
  routbnd.a(2, dir_width, btex \msgtwo etex);
endfig;

beginfig(2);
  % Backbone
  strand.a(2, origin, gamma, btex $\mathstrut\mathit{init}$ etex, node);

  % Messages
  outbnd.a(1, dir_width, btex \msgthree etex);
  inbnd.a(2, dir_width, btex \msgtwo etex);
endfig;

% Responder role

beginfig(3);
  % Backbone
  strand.b(2, origin, gamma, btex $\mathstrut\mathit{resp}$ etex, node);

  % Messages
  rinbnd.b(1, dir_width, btex \msgthree etex);
  routbnd.b(2, dir_width, btex \msgtwo etex);
endfig;

beginfig(4);
  % Backbones
  strand.b(2, origin, gamma,
    btex $\mathstrut\mathit{resp}$ etex, node);
  strand.a(1, (w, ypart b1.c), gamma,
    btex $\mathstrut\mathit{init}$ etex, node);

  boxit.o1(btex $\succ$ etex);
  o1.c = .5[b1.c,a1.c];
  draw pic o1;

  drawmsg(a1.w -- o1.e);
  drawmsg(o1.w -- b1.e);
  label.top(btex \msgfour etex, .5[a1.w,o1.e]);
  label.top(btex \msgone etex, .5[o1.w,b1.e]);
endfig;

beginfig(5);
  % Initial point-of-view
  strand.b(2, origin, gamma,
    btex $\mathstrut\textcolor{red}{\mathit{resp}}$ etex, node);
endfig;

beginfig(6);
  % Bundle
  strand.b(2, origin, gamma,
    btex $\mathstrut\mathit{resp}$ etex, node);
  strand.e(3, (2w/3, ypart b1.c), gamma,
    btex $\mathstrut\mathit{enc}$ etex, node);
  strand.g(1, (w/3, ypart e2.c), gamma,
    btex $\mathstrut\mathit{gen}$ etex, node);
  strand.d(3, (w/3, ypart e1.c), gamma,
    btex $\mathstrut\mathit{dec}$ etex, node);
  strand.h(1, (2w/3, ypart d2.c), gamma,
    btex $\mathstrut\mathit{gen}$ etex, node);
  strand.a(1, (w, ypart d1.c), gamma,
    btex $\mathstrut\mathit{init}$ etex, node);

  drawmsg(e3.w -- b1.e);
  label.top(btex \msgone etex, .5[e3.w,b1.e]);
  drawmsg(g1.e -- e2.w);
  label.top(btex \pubk{B} etex, .5[g1.e,e2.w]);
  drawmsg(d3.e -- e1.w);
  label.top(btex \msgsix etex, .5[d3.e,e1.w]);
  drawmsg(h1.w -- d2.e);
  label.top(btex \privk{B'} etex, .5[h1.w,d2.e]);
  drawmsg(a1.w -- d1.e);
  label.top(btex \msgfive etex, .5[a1.w,d1.e]);
endfig;

verbatimtex
\end{document}
etex
bye;
