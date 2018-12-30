
int: length; % length of Huang Gai's back
set of int: LENGTH = 1..length;
int: width; % width of Huang Gai's back
set of int: WIDTH = 1..width;

array[LENGTH,WIDTH] of bool: wound; % wound positions
int: total_wounds = sum(array1d(wound));

int: ntypes;  % number of types of plaster
set of int: TYPE = 1..ntypes;
array[TYPE] of int: number;          % number of plaster available
array[TYPE,1..2] of int: dim;        % dimensions of plaster
int: maxdim = max(array1d(dim));
array[TYPE] of int: price;

int: total = sum(number);
set of int: PLASTER = 1..total;
array[TYPE] of int: psum = [ sum(i in 1..t-1)(number[i]) | t in TYPE ];
array[PLASTER] of TYPE: t = [max(t in TYPE)(t*(p > psum[t])) | p in PLASTER];
array[PLASTER] of var LENGTH:  x;
array[PLASTER] of var WIDTH:   y;
enum USAGE = { Long, Wide, Not };
array[PLASTER] of var USAGE:   u;


include "diffn.mzn";
%(x,y,dx,dy) nonoverlapping
constraint diffn(x,y,len,wid);

% if we are not using the plaster
% we are going to use width of zero
array[PLASTER] of var 0..length: len =
               [ [ dim[t[p],1], dim[t[p],2], 0 ][u[p]]
                 | p in PLASTER];
array[PLASTER] of var 0..length: wid =
               [ [ dim[t[p],2], dim[t[p],1], 0 ][u[p]]
                 | p in PLASTER];

% 1.symmetry we can always interchange same plaster
include "lex_lesseq.mzn"; 
constraint forall(p in 1..total-1 where t[p] = t[p+1])
                    (lex_lesseq( [u[p], x[p], y[p]], [u[p+1], x[p+1], y[p+1]]));
% for every not used plaster we force it to be right in corner                           
constraint forall(p in PLASTER)
                  (u[p] = Not -> x[p] =1 /\ y[p] = 1);
% every wound must be coverd                  
constraint forall(l in LENGTH, w in WIDTH)
                  (wound[l,w] -> 
                   exists(p in PLASTER)
                         ( x[p] <= l/\ x[p] + len[p] > l /\
                           y[p] <= w /\ y[p] + wid[p] > w));  
% plaster not stick out
constraint forall(p in PLASTER)
                ( x[p] + len[p] - 1 <= length /\
                  y[p] + wid[p] - 1 <= width);
                           
% dominance: a 3x3 can always be changed to 1 2x1 and 1 2x2 and 1 3x1
array[TYPE] of var int: used = [ sum(p in PLASTER where t[p] = ty)(u[p] != Not) | ty in TYPE];

constraint  used[2] <= number[2] -1 /\ used[3] <= number[3] -1 
            /\ used[4] <= number[4] -1 -> used[5] = 0;
            
% var TYPE: donimated;
% % the area covered by what we are using has to be the same as the thing we are trying to dominate
% constraint sum(ty in TYPE)(used[ty]*dim[ty,1]*dim[ty,2]) = dim[dominated, 1] * dim[dominated,2];
% constraint forall(p in PLASTER)(x[p] + len[p] -1 <= dim[dominated,1] /\
%                                 y[p] + wid[p] - 1 <= dim[dominated,2]);

% var int: cost = sum(p in PLASTER)
%                    (price[t[p]] * (u[p] != Not));
var int: cost = sum(t in TYPE)(price[t] * used[t]);                                                                                      
                 
solve minimize cost;

output ["x = \(x);\ny = \(y);\nu = \(u);\ncost = \(cost);"];
 








