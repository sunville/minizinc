int: PROBLEM_STAGE; %Identifier to be used for each instance. If you write a MiniZinc model to solve the problem, this can be ignored.

int: n;
set of int: PERSON = 1..n;
int: k;
set of int: CAMPSITE = 1..k;
int: maxsize;
array[int,1..2] of int: ML; % 2 people from same family
array[int,1..2] of int: CL; % 2 people hate each other
set of int: FAMILY = index_set_1of2(ML);
set of int: DISLIKE = index_set_1of2(CL);
array[int,1..2] of PERSON: E;  % 2 people know each other
set of int: EDGE = index_set_1of2(E);
int: m = max(EDGE);
array[PERSON] of int: D = [sum(i in EDGE)(E[i,1] = p \/ E[i,2] = p) | p in PERSON]; % di be the number of people that person i knows.
array[PERSON] of var CAMPSITE: x; % assignment of campsite to each person
%var int: obj = sum(c in CAMPSITE)(4* m * sum(i in EDGE)(x[E[i,1]] = c /\ x[E[i,2]] = c) 
%                                     - pow(sum(i in PERSON)(D[i] * (x[i] = c)) ,2)); % harmony of the assignment

var int: obj = 4* m * sum(i in EDGE)(x[E[i,1]] = x[E[i,2]]) 
                                     - sum(c in CAMPSITE)(pow(sum(i in PERSON)(D[i] * (x[i] = c)) ,2));

% refugees in each campsite is less than maxsize;
%include "global_cardinality_low_up.mzn";
%constraint forall(i in CAMPSITE)(sum(j in PERSON)(x[j] = i) <= maxsize);
%constraint global_cardinality_low_up(x,[c|c in CAMPSITE],[0 | c in CAMPSITE],[maxsize | c in CAMPSITE]);

% break symmetry.
include "value_precede_chain.mzn";
constraint value_precede_chain([i | i in CAMPSITE],x);

include "int_set_channel.mzn";
array[CAMPSITE] of var set of PERSON: camp_p;
constraint int_set_channel(x, camp_p);
constraint forall(i in DISLIKE)
              (forall(j in CAMPSITE)
                      (CL[i,1] in camp_p[j] -> 
                       not (CL[i,2] in camp_p[j])));
constraint forall(i in FAMILY)
              (forall(j in CAMPSITE)
                      (ML[i,1] in camp_p[j] -> 
                       ML[i,2] in camp_p[j]));
array[CAMPSITE,PERSON] of var 0..1: camp_person;
constraint forall(c in CAMPSITE)
                (forall(p in PERSON) 
                       (camp_person[c,p] = (x[p] = c)));
constraint forall(c in CAMPSITE)(sum(p in PERSON)(camp_person[c,p]) <= maxsize);
constraint forall(p in PERSON)(sum(c in CAMPSITE)(camp_person[c,p]) = 1);
constraint forall(c in CAMPSITE)(forall(p in PERSON)(camp_person[c,p]=1 -> x[p] = c));
% pairs of people from the same family must be sent to the same camp
constraint forall(f in FAMILY)(x[ML[f,1]] = x[ML[f,2]]);

% pairs of people who dislike each other intently must be sent to dierent camp
constraint forall(d in DISLIKE)(x[CL[d,1]] != x[CL[d,2]]);

% Note that if it is more harmonious then Shennong will not use all the campsites


include "gecode.mzn";
annotation relax_and_reconstruct(array[int] of var int, int);
annotation restart_luby(int);
% dom_w_deg
solve :: seq_search([int_search(camp_person, dom_w_deg, indomain_random, complete),
                    int_search([obj], input_order, indomain_max, complete)])
      :: relax_and_reconstruct(array1d(camp_person) ++ x, 90)
      :: restart_luby(100)
      maximize obj;

output ["x = \(x);\nobj = \(obj);"];