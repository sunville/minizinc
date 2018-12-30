% Warning the village
int: n; % number of houses
set of int: HOUSE = 1..n; 
array[HOUSE] of int: x;
array[HOUSE] of int: y;
int: limit; % max time allowed

int: m; % number of messengers
set of int: MESSENGER = 1..m;
array[MESSENGER] of var HOUSE: messenger; % who are the messengers

% nodes
% 1..N are villagers
% n+1..n+m are end trip node
set of int: NODE = 1..n+m;
array[NODE] of var NODE: next;   % next node visited after this one
var 0..limit: endtime;


array[NODE] of var 0..limit:time; % the time messenger arrives at that house
array[NODE] of var MESSENGER: who; % keep track of who deliver message to each house

include "alldifferent.mzn";
constraint alldifferent(messenger);
constraint forall(i in 1..m-1)(messenger[i] < messenger[i+1]);

include "circuit.mzn";
constraint circuit(next);

%dummy house points at next messengers house
constraint forall(i in 1..m-1)(next[n+i] = messenger[i+1]);
constraint next[n+m] = messenger[1];

constraint forall(i in HOUSE)(time[next[i]] = time[i] + distance[i,next[i]]);
%keep track who visits each house
constraint forall(i in MESSENGER)(who[messenger[i]] = i);
constraint forall(i in HOUSE)(who[next[i]] = who[i]);

constraint forall(i in HOUSE)(messenger[who[i]] <= i);
% build distance array is tricky
array[HOUSE, NODE] of var 0..limit: distance = 
    array2d(HOUSE, NODE,
            [ if to in HOUSE then 
                abs(x[from] - x[to]) + abs(y[from] - y[to]) 
              else 
                abs(x[from] - x[messenger[who[from]]]) +
                abs(y[from] - y[messenger[who[from]]])
              endif
            | from in HOUSE, to in NODE]);

constraint forall(i in NODE)(time[i] <= endtime);

include "gecode.mzn";
annotation relax_and_reconstruct(array[int] of var int, int);
annotation restart_luby(int);

solve :: seq_search([int_search(next, dom_w_deg, indomain_random, complete),
                     int_search(messenger, input_order, indomain_min, complete)])
      :: relax_and_reconstruct(next, 80)
      :: restart_luby(100)
        minimize endtime;

output ["messenger = \(messenger);\nnext = \(next);\nendtime = \(endtime);\n"];
