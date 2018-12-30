% Preparing a banquet in the least time
enum COOK; % the set of cooks available
enum DISH; % the set of all dishes to prepare
int: no_tasks; % total number of tasks
set of int: TASK = 1..no_tasks;
array[DISH] of set of TASK: steps; % steps to making a dish
array[TASK, COOK] of int: time; % amount of time to complete task by cook

%int: maxt = sum(array1d(time));
int: maxt = sum(i in TASK)(max(j in COOK)(time[i,j]))-max(time);
set of int: TIME = 0..maxt;
array[TASK] of var TIME:s;  % start time for task
array[TASK] of var COOK:c;  % cook for task
var TIME: obj;

include "gecode.mzn";                                          
include "disjunctive.mzn";
include "cumulative.mzn";
% each dish has steps in order
constraint forall(tasks in steps)(forall(i,j in tasks where j>i)(s[i]+time[i,c[i]] <= s[j]));
% each step needs one of the cooks who can do it
constraint forall(i in TASK)(time[i, c[i]] > 0);
% each cook can only be doing one thing at a time
constraint forall(i in COOK)(
  let{array[int] of var int:
        ss = [s[t] * (c[t] = i) | t in TASK];
      array[int] of var int:
        dd = [time[t,i] * (c[t] = i) | t in TASK];}
  in disjunctive(ss,dd));
%constraint cumulative(s,[1| t in TASK], [1 | t in TASK], length(COOK));
% get obj
constraint obj = max(i in TASK)(s[i] + time[i,c[i]]);
% search
%ann: search =int_search(s, dom_w_deg, indomain_min, complete);
% ann: search =int_search(c,dom_w_deg, indomain_random, complete);
annotation relax_and_reconstruct(array[int] of var int, int);
annotation restart_luby(int);
ann: search = seq_search([int_search(c, dom_w_deg, indomain_random, complete),
                         int_search(s, dom_w_deg, indomain_min, complete),
                         int_search([obj], input_order, indomain_min, complete)]);

ann: restart = restart_luby(80);
solve :: search
      :: relax_and_reconstruct(c , 70)
      :: restart
      minimize obj;

output ["s = ",show(s),";\n"] ++
       ["c = ",show(c),";\n"] ++
       ["obj = ",show(obj),";"];
       