filenametemplate "%j-%c.mps";

verbatimtex
\documentclass[12pt]{article}
\newcommand{\enc}[2]{\{\!|#1|\!\}_{#2}}
\begin{document}
etex

numeric base_width;
begingroup;
  path p; p = bbox(btex $\strut$ etex rotated 90);
  base_width = 1.3 xpart (lrcorner p - llcorner p);
endgroup;

input boxes;

beginfig(0);
  boxit.b1(btex $X_\top$ etex);
  boxit.b2(btex $\mathsf{text}$ etex rotated 90);
  boxit.b3(btex $\mathsf{data}$ etex rotated 90);
  boxit.b4(btex $\mathsf{name}$ etex rotated 90);
  boxit.b5(btex $\mathsf{akey}$ etex rotated 90);
  boxit.b6(btex $\mathsf{skey}$ etex rotated 90);
  boxit.b7(btex $\mathsf{tags}$ etex rotated 90);

  b4.s = origin;

  for i = 1 upto 6:
    b[i].sw=b[i+1].se;
    b[i].nw=b[i+1].ne;
  endfor;

  for i = 1 upto 7:
    b[i].e + (base_width, 0) = b[i].w;
  endfor;

  for i = 4 upto 6:
    drawboxed(b[i]);
  endfor;

  for i = 3 downto 2:
    drawboxed(b[i]);
  endfor;

  draw pic b[1];
  draw pic b[7];

  % Top of triangle contrained to force a right triange
  z1 = b4.n - b4.s + (b7.nw - b4.n) rotated 90;

  ypart z2 = ypart z3 = 0;
  z2 = whatever[b7.nw,z1];
  z3 = whatever[b1.ne,z1];

  draw z1--z2--z3--z1;

  label(btex \begin{tabular}{c}pairings\\[1ex]
    encryptions\end{tabular} etex, .5z1);
endfig;

verbatimtex
\end{document}
etex
bye;
