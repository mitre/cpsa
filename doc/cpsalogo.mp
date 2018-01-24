outputformat := "svg";
outputtemplate := "%j.svg";
prologues := 3;

verbatimtex
\documentclass[12pt]{article}
\begin{document}
etex

input boxes;

input strands;

input cmstrands;		% Use CM arrows

color mitreblue;
mitreblue      = (0,70/255,174/255); % MITRE blue PMS 293 Blue

picture node; node = btex $\bullet$ etex;

% The height of a downarrow is the unit of length for a strand
% succession edge.

numeric delta;
begingroup;
  path p; p = bbox(btex $\downarrow$ etex);
  delta = ypart(ulcorner p - llcorner p);
endgroup;

pair w; w = (2cm, 0);		% Width of diagram

beginfig(1);

    % Strand for principal A
  strand.a(2, origin, delta, node, node);

  % Strand for principal B
  strand.b(2, w, delta, node, node);

  drawmsg(a1.e -- b1.w);
  drawmsg(b2.w -- a2.e);

  boxit.t(btex \Large\sf CPSA etex); t.c = .5[a2.c, b1.c];
  draw pic t withcolor mitreblue;

endfig;

verbatimtex
\end{document}
etex
bye;
