% Strand macros

%% John D. Ramsdell--May 2008,
%% The MITRE Corporation, Bedford, MA.

% For simple drawings, use the strand macro.

% Use these macros when drawing strand edges.  The cmstrands package
% redefines these two macros.

% Draw a message edge
def drawmsg(expr p) =
  drawarrow p;
enddef;

% Draw a strand succession edge.  The arrow head is drawn, not filled.
% Based on "Hints and Tricks" in TUGboat, Volume 19 (1998), No. 2, by
% Jeremy Gibbons.
def drawsucc(expr p) =
  draw arrowhead p;
  path q;
  q := fullcircle scaled (2*ahlength)
    shifted (point (length p) of p);
  numeric tp, tq;
  (tp,tq) = p intersectiontimes q;
  draw subpath (0, tp) of p;
enddef;

% Draw a message edge with a dashed line.  Used sometimes for when the
% source and the distination message differ.
def drawdashedmsg(expr p) =
  drawarrow p dashed evenly scaled 3;
enddef;

% Strand drawing macros

% Box the nodes of a strand.  The origin of the strand is the center
% of the last strand node.  The name is a picture for the first node,
% and node is a picture for the successive nodes.
vardef boxstrand@#(expr height, origin, name, node) =
  boxit.@#1(name);
  for i = 2 upto height:
    boxit.@#[i](node);
    xpart @#[i-1].s = xpart @#[i].n;
  endfor;
  @#[height].c = origin;
enddef;

% Space a pair of strand nodes using the given height and separation
% delta.
vardef spacestrand@#(expr pos, delta) =
  ypart @#[pos].s = delta + ypart @#[pos+1].n;
enddef;

% Layout strand by making the distance been successive nodes the given
% separation delta.
vardef layoutstrand@#(expr height, delta) =
  for i = 1 upto height - 1:
    spacestrand@#(i, delta);
  endfor;
enddef;

% Link the nodes of a strand.
vardef linkstrand@#(expr height) =
  for i = 2 upto height:
    drawsucc(@#[i-1].s -- @#[i].n);
  endfor;
enddef;

% Draw a strand with equally spaced nodes.  The origin of the strand
% is the center of the last strand node.  The the distance between
% successive nodes is delta.  The name is a picture for the first
% node, and node is a picture for the successive nodes.

% A strand is drawn bottom up because the size of the label in the
% first box may vary.

vardef strand@#(expr height, origin, delta, name, node) =
  boxstrand@#(height, origin, name, node);
  layoutstrand@#(height, delta);
  for i = height downto 1:
    draw pic @#[i];
  endfor;
  linkstrand@#(height);
enddef;

% layout a strand but don't draw it.
vardef phantomstrand@#(expr height, origin, delta, name, node) =
  boxstrand@#(height, origin, name, node);
  layoutstrand@#(height, delta);
  for i = height downto 1:
    fixsize(@#[i]);
  endfor;
enddef;

% Event macros used while displaying roles.

% Draw an inbound term at a given strand position.
% The width is the length of the first arrow.
vardef inbnd@#(expr pos, width, term) =
  pair d;
  d = (xpart @#[1].e + width, ypart @#[pos].e);
  drawmsg(d .. @#[pos].e);
  label.rt(term, d);
enddef;

% Draw an outbound term at a given strand position.
% The width is the length of the first arrow.
vardef outbnd@#(expr pos, width, term) =
  pair d;
  d = (xpart @#[1].e + width, ypart @#[pos].e);
  drawmsg(@#[pos].e .. d);
  label.rt(term, d);
enddef;

% Reverse versions:
vardef rinbnd@#(expr pos, width, term) =
  pair d;
  d = (xpart @#[1].w - width, ypart @#[pos].w);
  drawmsg(d .. @#[pos].w);
  label.lft(term, d);
enddef;

vardef routbnd@#(expr pos, width, term) =
  pair d;
  d = (xpart @#[1].w - width, ypart @#[pos].w);
  drawmsg(@#[pos].w .. d);
  label.lft(term, d);
enddef;
