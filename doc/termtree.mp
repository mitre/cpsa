filenametemplate "%j-%c.mps";

verbatimtex
\documentclass[12pt]{article}
\newcommand{\enc}{\ensuremath{\mathsf{enc}}}
\newcommand{\pair}{\ensuremath{\mathsf{pair}}}
\newcommand{\pubk}{\ensuremath{\mathsf{pubk}}}
%\newcommand{\enc}{\ensuremath{\{\!|\cdot|\!\}_{(\cdot)}}}
%\newcommand{\pair}{\ensuremath{(\cdot,\cdot)}}
%\newcommand{\pubk}{\ensuremath{K_{(\cdot)}}}
\begin{document}
etex

beginfig(0);
  h = -1cm;
  w = 1cm;
  z0 = origin;
  z1 = z0 + (-1.5w, h);
  z2 = z1 + (-.5w, h);
  z3 = z1 + (.5w, h);
  z4 = z3 + (0, h);
  z5 = z0 + (1.5w, h);
  z6 = z5 + (-w, h);
  z7 = z6 + (-.5w, h);
  z8 = z6 + (.5w, h);
  z9 = z8 + (0, h);
  z10 = z5 + (w, h);
  z11 = z10 + (0, h);

  draw z0--z1;
  draw z1--z2;
  draw z1--z3;
  draw z3--z4;
  draw z0--z5;
  draw z5--z6;
  draw z6--z7;
  draw z6--z8;
  draw z8--z9;
  draw z5--z10;
  draw z10--z11;

  pickup pencircle scaled 4pt;
  dotlabel.rt(btex ~~\pair etex, z0);
  dotlabel.rt(btex ~~\enc etex, z1);
  dotlabel.rt(btex ~$x$ etex, z2);
  dotlabel.rt(btex ~\pubk etex, z3);
  dotlabel.rt(btex ~$a$ etex, z4);
  dotlabel.rt(btex ~\enc etex, z5);
  dotlabel.rt(btex ~\enc etex, z6);
  dotlabel.rt(btex ~$x$ etex, z7);
  dotlabel.rt(btex ~\pubk etex, z8);
  dotlabel.rt(btex ~$a$ etex, z9);
  dotlabel.rt(btex ~\pubk etex, z10);
  dotlabel.rt(btex ~$b$ etex, z11);
endfig;

verbatimtex
\end{document}
etex
bye;
