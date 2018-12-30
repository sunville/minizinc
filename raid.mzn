enum WARRIOR;
WARRIOR: dummy; 
enum CLAN; 

int: l;
int: u;
int: m;

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;
array[CLAN,CLAN] of 0..1: hates;

var int: Total_Strength;

constraint sum(i,j in raid where i<j)(hates[clan[i],clan[j]])<=m;
constraint Total_Strength=sum(i in raid)(strength[i]);


array[1..u] of var WARRIOR: raid;
constraint forall(i in 1..u-1)( raid[i]>=raid[i+1]+(raid[i]!=dummy));
constraint forall(i in 1..l)(raid[i]!=dummy);
output["raid = {"] ++ [if fix(raid[i]) != dummy then show(raid[i])
                       ++ if i < u /\ fix(raid[i+1]) != dummy then ", " else "" endif
                       else "" endif | i in 1..u ] ++ ["};\noutput = \(Total_Strength);"];

solve maximize Total_Strength;