int: n;  % number of soldiers
set of int: SOLDIER = 1..n;
set of int: POS = 1..n;
array[SOLDIER] of int: height;
int: cols;    % number of columns of soldiers 
int: delta;   % height delta allowed

array[POS] of var SOLDIER: soldier;

%first is captain
constraint soldier[1] = 1;

var 1 ..n:obj;
%
constraint forall(i in SOLDIER)(height[i] = soldier[])
utput ["pos = ", show(makespan), ";\n" ] ++
       ["obj = ", show(obj), ";"]; 
