filenametemplate "%j-%c.mps";

% Original comment in the METAFONT version of the MITRE logo.

%% The MITRE logo version 1.1 released 11/16/89.

%% Created by Richard Shaeff --- 1981
%% Shaeff Design Inc, Needham, MA
%%
%% Programmed in METAFONT by John D. Ramsdell --- November 1989
%% The MITRE Corporation, Bedford, MA
%% Copyright 1989 by The MITRE Corporation.

%% Richard Shaeff's original design was done by creating an
%% outline.  Therefore, this METAFONT version generates letters
%% by filling an outlined region.

%% The program expects ht# and only ht# to be defined in a
%% parameter file.  All other parameters are derived from this
%% one.  This is in conformance with the MITRE policy which states
%% that the logo may be changed only by linearly scaling all of
%% the logo's dimensions.

% The single parameter in METAPOST is h.
h=15pt;

%% Note:
%% Measurements from the original design and are in inches.
%% The height of the logo is 4.25 inches and that height is
%% used to scale all dimensions.
%%

%% MITRE blue is Pantone Matching System (PMS) 293 Blue, with an RGB
%% value of (0, 81, 186).

prologue:=1;

I_w            = 0.87500/4.25h;      % I width. (7/8in)
T_bar_h        = 0.78125/4.25h;      % T bar height. (25/32in)
T_lft_w        = 1.03125/4.25h;      % Left T bar. (1 1/32in)
T_rt_w         = 1.00000/4.25h;      % Right T bar. (1in)
E_gap_h        = 0.93750/4.25h;      % Upper E gap. (15/16in)
E_bar_shrink_h = 0.06250/4.25h;      % Mid bar shrink. (1/16in)
E_bar_w        = 1.56250/4.25h;      % E bar width. (1 9/16in)
R_tail_a       = 125;                % R tail angle.
M_vee_h        = 1.62500/4.25h;      % M vee height. (1 5/8in)
M_vee_a        = 70;                 % M vee angle.
M_edge_a       = 100;                % M edge angle.
M_w            = 5.25000/4.25h;      % M width. (5 1/4in)
skip_w         = 0.12500/4.25h;      % Distance between T and R.
                                     % (1/8in)
s = max(1, round(skip_w));           % Rounded interletter space.
color mitreblue;
mitreblue      = (0,70/255,174/255); % MITRE blue PMS 293 Blue

def draw_M(expr o) =
  begingroup
    save x, y;
    w = M_w + skip_w;
    x1 = o;
    y2 = y3 = y5 = y6 = h;
    y4 = h - y12 = h - y9 = M_vee_h;       % The vee heights are the same.
    y1 = y13 = y11 = y10 = y8 = y7 = 0;

    x13 = x1 + I_w;
    x7 = w - max(1, round(.5skip_w));
    x8 = x7 - I_w;
    x3 - x2 = x6 - x5;                     % Top edges widths are the same.
    x5 - x2 = x10 - x1;                    % A strange fact---measure it!

    z6 = z7 + whatever * dir M_edge_a;     % The right side has all nice
    z9 = z8 + whatever * dir M_edge_a;     % and neat angles defining it.
    z10 = z9 + whatever * dir M_vee_a;
    z4 = (-I_w, 0) + whatever[z10,z9];     % Width of right diagonal is I_w.
    z5 = z4 + whatever * dir M_vee_a;
    z12 = z13 + whatever * (z2 - z1);
    z11 = z12 + whatever * (z3 - z4);
    % The width of the left diagonal is only approximately I_w.
    % The following is only "almost" true.
    % z4 = (I_w, 0) + whatever[z11,z12];

    fill z1--z2--z3--z4--z5--z6--z7
    & z7--z8--z9--z10--z11--z12--z13--cycle withcolor mitreblue;
    w
  endgroup;
enddef;

def draw_I(expr o) =
  begingroup
    save x, y;
    y2 = y3 = h;
    y1 = y4 = 0;

    x1 = x2 = o;
    x3 = x4 = o + round(I_w);

    fill z1--z2--z3--z4--cycle withcolor mitreblue;
    x3 + s
  endgroup;
enddef;

def draw_T(expr o) =
  begingroup;
    save x, y;
    y4 = y5 = h;
    y3 = y2 = y7 = y6 = h - T_bar_h;
    y1 = y8 = 0;

    x3 = x4 = o;
    x2 = x1 = o + round(T_lft_w);
    x7 = x8 = o + round(T_lft_w + I_w);
    x6 = x5 = o + round(T_lft_w + I_w + T_rt_w);

    fill z1--z2--z3--z4--z5--z6--z7--z8--cycle withcolor mitreblue;
    x6 + s
  endgroup;
enddef;

def draw_R(expr o) =
  begingroup;
    save x, y;
    y2 = y3 = h;
    y10 = y11 = h - T_bar_h;       % y10, y8, y5, y3 must be integers.
    y9 = y4 = y10 - .5E_gap_h;     % They help determine the position
    y7 = y15 = y8 = y10 - E_gap_h; % of horizontal tangents to curves.
    y6 = y5 = y7 - (T_bar_h - E_bar_shrink_h);
    y1 = y12 = y13 = y16 = 0;

    x1 = x2 = o;
    x11 = x12 = o + round(I_w);	   % The space in the "R" must be the
    x7 = x6 = x14 = x11 + s;       % same as the interletter space.
    x3 = x10 = x8 = x5 = o + I_w + y7 - y 14;  % The location of the tail
    x13 = x3 + .5E_gap_h;          % (x13) must not be rounded or
                                % METAFONT cannot solve the equations.
    z14 = z13 + whatever * dir R_tail_a;
    z16 = (x13+I_w+skip_w, skip_w) + whatever * dir R_tail_a;
    z15 = z16 + whatever * dir R_tail_a;

    x9 = round(x13);               % x4 and x9 determine vertical tangents
    x4 = round(x13 + I_w);         % so they must be integers.

    fill z1--z2--z3
    & z3{z3-z2}..z4{z5-z3}..{z6-z5}z5
    & z5--z6--z7--z8
    & z8{z8-z7}..z9{z10-z8}..{z11-z10}z10
    & z10--z11--z12--cycle withcolor mitreblue;

    % "R" Tail
    fill z13--z14--z7--z15--z16--cycle withcolor mitreblue;
    x4 + s
  endgroup;
enddef;

def draw_E(expr o) =
  begingroup;
    save x, y;
    y2 = y3 = h;
    y5 = y4 = h - T_bar_h;
    y6 = y7 = y5 - E_gap_h;
    y9 = y8 = y6 - (T_bar_h - E_bar_shrink_h);
    % Notice that the lower bar is bigger than the upper one.
    y10 = y11 = T_bar_h + E_bar_shrink_h;
    y1 = y12 = 0;

    x1 = x2 = o;
    x5 = x6 = x9 = x10 = o + round(I_w);
    x3 = x4 = x7 = x8 = x11 = x12 = o + round(I_w + E_bar_w);

    fill z1--z2--z3--z4--z5--z6--z7--z8
    & z8--z9--z10--z11--z12--cycle withcolor mitreblue;
    x3 + max(1, round(.5skip_w))
  endgroup;
enddef;

beginfig(0);
  x1 = draw_M(0);
  x2 = draw_I(x1);
  x3 = draw_T(x2);
  x4 = draw_R(x3);
  x5 = draw_E(x4);
endfig;
bye;
