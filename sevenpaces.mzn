var 1..9: S;
var 0..9: E;
var 1..9: V;
var 0..9: N;
var 1..9: P;
var 0..9: A;
var 0..9: C;
var 0..9: R;
include "alldifferent.mzn";
constraint alldifferent([S,E,V,N,P,A,C,R]);
constraint S*10000 + E*1000 + V*100 + E*10 + N
           + P*10000 + A*1000 + C*100 + E*10 + S
           = V*10000 + E*1000 + R*100 + S*10 + E;
solve maximize V*10000 + E*1000 + R*100 + S*10 + E;