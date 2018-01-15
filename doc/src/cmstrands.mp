% CM strand arrows for documents

% Use the cmarrows package if you want double arrows for strand
% succession edges.

input cmarrows;

setup_cmarrows(
  arrow_name = "doublearrow";
  parameter_file = "cmr12.mf";
  macro_name = "drawdubarrow");

def drawsucc(expr p) =
  drawdubarrow p;
enddef;

setup_cmarrows(
  arrow_name = "texarrow";
  parameter_file = "cmr12.mf";
  macro_name = "drawtexarrow");

def drawmsg(expr p) =
  drawtexarrow p;
enddef;
