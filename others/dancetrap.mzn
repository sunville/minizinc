% Beauty Trap
% Perform the most seductive dance

enum LEGS = {spin, leap, waltz, curtsey, prep, stand};
enum ARMS = {beckon, out, up, wrapped, neutral};
enum FACE = {smile, wink, batt, think, glow, blank};

int: maxlen;
set of int: STEP = 1..maxlen;
array[LEGS] of int: maxlegs;
array[ARMS] of int: maxarms;
array[FACE] of int: maxface;
constraint assert(maxlegs[stand] >= maxlen, "maxlegs[stand] smaller than maxlen");
constraint assert(maxarms[neutral] >= maxlen, "maxarms[neutral] smaller than maxlen");
constraint assert(maxface[blank] >= maxlen, "maxface[blank] smaller than maxlen");
array[LEGS,ARMS] of int: dance_value;
array[ARMS,FACE] of int: entice_value;
constraint assert(dance_value[stand,neutral] = 0, "incorrect dance_value array");
constraint assert(entice_value[neutral,blank] = 0, "incorrect entice_value array");
int: boredom; % how bored each step make the viewer

var STEP: len;
array[STEP] of var LEGS: legs;
array[STEP] of var ARMS: arms;
array[STEP] of var FACE: face;
var int: obj;
%constraint
%upper limits on same moves
include "global_cardinality_low_up.mzn";
constraint global_cardinality_low_up(legs,LEGS,[0,0,0,0,0,1],maxlegs);
constraint global_cardinality_low_up(arms,ARMS,[0,0,0,0,1],maxarms);
constraint global_cardinality_low_up(face,FACE,[0,0,0,0,0,1],maxface);
%avoid impossible combination
constraint forall(i in 1..len)(dance_value[legs[i],arms[i]] >= 0);
constraint forall(i in 1..len)(entice_value[arms[i],face[i]] >= 0);
%regular constraint on legs
include "regular.mzn";
constraint regular([legs[i] | i in STEP], 7, 6, ld, 1, {7});
array[1..7, LEGS] of 0..7: ld=
                           [|2,0,4,5,6,7
                            |0,0,0,5,6,7
                            |2,0,4,0,0,7
                            |2,0,4,0,6,7
                            |2,0,4,5,0,7
                            |2,3,4,5,6,7
                            |2,0,4,5,6,7|];
constraint forall(i in 1..maxlen-3)(legs[i] = waltz /\ legs[i+1] = waltz /\ legs[i+2] = waltz -> legs[i+3] != waltz);
constraint forall(i in 1..maxlen-1)(legs[i]=waltz -> forall(j in i+1..maxlen)(legs[j] =curtsey -> 
                                    exists(k in i+1..j-1)(legs[k] = stand)));
%constraints on arms
constraint regular([arms[i] | i in STEP], 6, 5, ad, 1, {6});
array[1..6, ARMS] of 0..6: ad=
                            [|0,3,4,5,6
                             |0,3,4,5,6
                             |2,0,4,0,6
                             |2,3,0,0,6
                             |0,3,4,0,6
                             |0,3,4,5,6|];
%constraints on face
constraint regular([face[i] | i in STEP],7,6,fd,1,{7});
array[1..7, FACE] of 0..7: fd=
                            [|2,3,4,5,6,7
                             |2,3,4,0,6,7
                             |2,3,4,5,6,7
                             |2,3,4,0,6,7
                             |2,3,4,5,6,7
                             |2,3,4,5,6,7
                             |2,3,4,5,6,7|];
constraint forall(i in 1..maxlen-2)(face[i] = face[i+1] /\ face[i] != blank -> face[i+2] != face[i]);
%len constraint
constraint forall(i in len+1..maxlen)(legs[i]=stand/\arms[i]=neutral/\face[i]=blank);
%obj
obj = sum(i in STEP)(dance_value[legs[i],arms[i]]) + sum(i in STEP)(entice_value[arms[i],face[i]])
      - len * boredom;
solve maximize obj;
output["len = ",show(len),";\n"];
output["legs = ",show(legs),";\n"];
output["arms = ",show(arms),";\n"];
output["face = ",show(face),";\n"];
output["obj = ",show(obj)];
