int: length; % height of lake
set of int: LENGTH = 0..length-1;
int: width; % width of lake
set of int: WIDTH = 0..width-1;

int: ntypes;  % number of types of ship
set of int: TYPE = 1..ntypes;
array[TYPE] of int: number;         % number of each type of ship
array[TYPE] of set of SHAPE: config; % configs for each type of ship
                                     % ship -> set of possible shapes 

int: nshapes; % number of shapes
set of int: SHAPE = 1..nshapes;
set of int: SHAPE0 = 0..nshapes;
array[SHAPE] of set of ROFF: shape;

int: nroff; % number of rectangle offsets
set of int: ROFF = 1..nroff;
array[ROFF,1..4] of int: rectoff; % x offset, y offset, width, height

int: total_ships = sum(number);
set of int: SHIP = 1..total_ships;
array[SHIP] of var LENGTH:  x;
array[SHIP] of var WIDTH:   y;
array[SHIP] of var SHAPE0:  k;

array[LENGTH] of WIDTH: mist; % mist starts at this width, goes downward
array[WIDTH] of int: arrow;  % number of arrows that arrive at this height
array[TYPE] of int: price;
int: budget;
enum STAGE = {A,B,C,D,E,F};
STAGE: stage;


var int: tarrows;

include "diffn.mzn";
include "lex_lesseq.mzn";
include "geost.mzn";
array[TYPE] of int: ssum = [ sum(i in 1..t-1)(number[i]) | t in TYPE ];
array[SHIP] of TYPE: t = [max(t in TYPE)(t*(s > ssum[t])) | s in SHIP];
array[SHIP] of var 1..width: wid;
array[SHIP] of var 1..length: len; 

constraint len = [ rectoff[t[s],3] | s in SHIP];
constraint wid = [ rectoff[t[s],4] | s in SHIP]; 
array[ROFF, 1..2] of int: rect_size = array2d(ROFF, 1..2, [rectoff[i,j] | i in ROFF, j in 3..4]);
array[ROFF, 1..2] of int: rect_offset = array2d(ROFF, 1..2, [rectoff[i,j] | i in ROFF, j in 1..2]);
array[SHIP, 1..2] of var int: base_position;
constraint stage != A -> forall(i in SHIP)(base_position[i,1] = x[i] /\ base_position[i,2] = y[i]);                                     
% if stage == A then
constraint stage = A -> diffn(x,y,len,wid);
constraint stage = A -> forall(s in SHIP)
                ( x[s] + rectoff[t[s],3] <= length /\
                  y[s] + rectoff[t[s],4] <= width);
constraint stage = A -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]]));                  
constraint stage = A -> forall(s in SHIP)(k[s] = t[s]);
constraint stage = A -> tarrows = 0;
include "cumulative.mzn";
constraint stage = A -> cumulative(x,len,wid,width);
constraint stage = A -> cumulative(y,wid,len,length);

% else if stage == B then
array[SHIP] of var SHAPE: kind;
constraint stage = B -> forall(s in SHIP)(kind[s] = t[s]);
constraint stage = B -> geost_bb(2,
                              rect_size,
                              rect_offset,
                              shape,
                              base_position,
                              kind,
                              [0,0],
                              [length,width]
                              );
constraint stage = B -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]]));                              
constraint stage = B -> forall(s in SHIP)(k[s] = t[s]);
constraint stage = B -> tarrows = 0;

% else if stage == C then
% ship always in fog
constraint stage = C -> forall(s in SHIP)(kind[s] = t[s]);
constraint stage = C -> if sum(mist)>0 
                  then
                  diffn([x[s] + rect_offset[roff,1] | s in SHIP, roff in shape[t[s]]]++[i | i in LENGTH],
                 [y[s] + rect_offset[roff,2] | s in SHIP, roff in shape[t[s]]]++[0 | i in LENGTH],
                 [rect_size[roff,1] | s in SHIP, roff in shape[t[s]] ] ++ [1 | i in LENGTH],
                 [rect_size[roff,2] | s in SHIP, roff in shape[t[s]] ] ++ [height | height in mist]) /\
                 forall(s in SHIP)(forall(rect in shape[t[s]])
                 (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
                  y[s] + rectoff[rect,2]+rectoff[rect,4] <= width))
                 else
                 geost_bb(2,
                              rect_size,
                              rect_offset,
                              shape,
                              base_position,
                              kind,
                              [0,0],
                              [length,width]
                              )
                 endif;   
% constraint stage = C ->
%                   diffn([x[s] + rect_offset[roff,1] | s in SHIP, roff in shape[t[s]]]++[i | i in LENGTH],
%                  [y[s] + rect_offset[roff,2] | s in SHIP, roff in shape[t[s]]]++[0 | i in LENGTH],
%                  [rect_size[roff,1] | s in SHIP, roff in shape[t[s]] ] ++ [1 | i in LENGTH],
%                  [rect_size[roff,2] | s in SHIP, roff in shape[t[s]] ] ++ [height | height in mist]) /\
%                  forall(s in SHIP)(forall(rect in shape[t[s]])
%                  (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
%                   y[s] + rectoff[rect,2]+rectoff[rect,4] <= width));                           
constraint stage = C -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]])); 
constraint stage = C -> tarrows = 0;
constraint stage = C -> forall(s in SHIP)(k[s] = t[s]);
% else if stage == D then
constraint stage = D -> forall(s in SHIP)(kind[s] = t[s]);
constraint stage = D -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]])); 
%constraint stage = A -> forall(s in SHIP)
%                 ( x[s] + rectoff[t[s],3] <= length /\
%                   y[s] + rectoff[t[s],4] <= width);                          
% constraint stage = D -> if sum(mist)>0 then
%                   diffn([x[s] + rect_offset[roff,1] | s in SHIP, roff in shape[t[s]]]++[i | i in LENGTH],
%                  [y[s] + rect_offset[roff,2] | s in SHIP, roff in shape[t[s]]]++[0 | i in LENGTH],
%                  [rect_size[roff,1] | s in SHIP, roff in shape[t[s]] ] ++ [1 | i in LENGTH],
%                  [rect_size[roff,2] | s in SHIP, roff in shape[t[s]] ] ++ [height | height in mist]) /\
%                  forall(s in SHIP)(forall(rect in shape[t[s]])
%                  (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
%                   y[s] + rectoff[rect,2]+rectoff[rect,4] <= width))
%                  else
%                  geost_bb(2,
%                               rect_size,
%                               rect_offset,
%                               shape,
%                               base_position,
%                               kind,
%                               [0,0],
%                               [length,width]
%                               )
%                  endif;
 constraint stage = D -> diffn([x[s] + rect_offset[roff,1] | s in SHIP, roff in shape[t[s]]]++[i | i in LENGTH],
                 [y[s] + rect_offset[roff,2] | s in SHIP, roff in shape[t[s]]]++[0 | i in LENGTH],
                 [rect_size[roff,1] | s in SHIP, roff in shape[t[s]] ] ++ [1 | i in LENGTH],
                 [rect_size[roff,2] | s in SHIP, roff in shape[t[s]] ] ++ [height | height in mist]);
              
 constraint stage = D -> forall(s in SHIP)(forall(rect in shape[t[s]])
                 (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
                  y[s] + rectoff[rect,2]+rectoff[rect,4] <= width));                
constraint stage = D -> forall(s in SHIP)(k[s] = t[s]);
constraint stage = D -> tarrows = sum(s in SHIP)
                                   (sum(roff in shape[t[s]])
                                     (sum(j in (y[s] + rectoff[roff,2])..(y[s]+rectoff[roff,2] + rectoff[roff,4] - 1))
                                         (if j < width then arrow[j] * rectoff[roff,3] else 0 endif)));                 

% else if stage == E then
constraint stage = E -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]]));
constraint stage = E -> forall(s in SHIP)(k[s] in config[t[s]]);
     
constraint stage = E -> diffn([(x[s] + rect_offset[roff,1]) * (roff in shape[k[s]]) | s in SHIP, roff in ROFF]++[i | i in LENGTH],
                 [(y[s] + rect_offset[roff,2]) * (roff in shape[k[s]]) | s in SHIP, roff in ROFF]++[0 | i in LENGTH],
                 [rect_size[roff,1]* (roff in shape[k[s]]) | s in SHIP, roff in ROFF] ++ [1 | i in LENGTH],
                 [rect_size[roff,2]* (roff in shape[k[s]]) | s in SHIP, roff in ROFF] ++ [height | height in mist]);
                              
 constraint stage = E -> forall(s in SHIP)(forall(rect in shape[k[s]])
                 (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
                  y[s] + rectoff[rect,2]+rectoff[rect,4] <= width));   

constraint stage = E -> tarrows = sum(s in SHIP)
                                   (sum(roff in shape[k[s]])
                                     (sum(j in y[s] + rectoff[roff,2]..y[s]+rectoff[roff,2] + rectoff[roff,4] - 1)
                                          %(arrow[j] * rectoff[roff,3])));
                                         (if j < width then arrow[j] * rectoff[roff,3] else 0 endif))); 

% else if stage == F then

constraint stage = F -> forall(s in 1..total_ships-1 where t[s] = t[s+1])
                          (lex_lesseq( [k[s], x[s], y[s]], [k[s+1], x[s+1], y[s+1]]));
constraint stage = F -> forall(s in SHIP)(k[s] in config[t[s]] \/ k[s] = 0);

 constraint stage = F -> forall(s in SHIP)(forall(rect in shape[k[s]] where k[s] > 0)
                 (x[s] + rectoff[rect,1]+rectoff[rect,3] <= length /\
                  y[s] + rectoff[rect,2]+rectoff[rect,4] <= width)); 

array[SHAPE0] of var set of int: shape0;
constraint stage = F -> forall(i in SHAPE)(shape0[i] = shape[i]);
constraint stage = F -> shape0[0] = {0};
array[0..nroff, 1..2] of int: rect_offset0 = array2d(0..nroff, 1..2, [0,0] ++ [rectoff[i,j] | i in ROFF, j in 1..2]);
array[0..nroff, 1..2] of int: rect_size0 = array2d(0..nroff, 1..2, [0,0] ++ [rectoff[i,j] | i in ROFF, j in 3..4]);

constraint stage = F -> diffn([(x[s] + rect_offset0[roff,1]) * (roff in shape[k[s]]) | s in SHIP, roff in ROFF]++[i | i in LENGTH],
                 [(y[s] + rect_offset0[roff,2]) * (roff in shape[k[s]]) | s in SHIP, roff in ROFF]++[0 | i in LENGTH],
                 [rect_size0[roff,1]* (roff in shape[k[s]]) | s in SHIP, roff in ROFF] ++ [1 | i in LENGTH],
                 [rect_size0[roff,2]* (roff in shape[k[s]]) | s in SHIP, roff in ROFF] ++ [height | height in mist]);    
                              
constraint stage = F -> tarrows = sum(s in SHIP)
                                   (sum(roff in shape[k[s]] where k[s] > 0)
                                     (sum(j in y[s] + rectoff[roff,2]..y[s]+rectoff[roff,2] + rectoff[roff,4] - 1)
                                         (if j < width then arrow[j] * rectoff[roff,3] else 0 endif))); 
constraint stage = F -> (sum(s in SHIP)(price[t[s]]*(k[s]>0)) <= budget);

include "gecode.mzn";
annotation restart_luby(int);
annotation relax_and_reconstruct(array[int] of var int, int);
             
solve 
  ::int_search(k, dom_w_deg,indomain_random,complete)
  ::relax_and_reconstruct(k,80)
  maximize tarrows;
output ["x = \(x);\ny = \(y);\nk = \(k);\ntarrows = \(tarrows);"];





