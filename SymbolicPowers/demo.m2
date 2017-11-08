restart
uninstallPackage "SymbolicPowers"
path = append(path,"~/Documents/Workshop-2017-Berkeley/SymbolicPowers");
installPackage "SymbolicPowers"


--Computing Symbolic Powers
restart
loadPackage "SymbolicPowers"
A = QQ[x,y,z];
I = intersect(ideal(x,y), ideal(x,z), ideal(y,z))
time symbolicPower(I,2)


--fermat configuration
restart
loadPackage "SymbolicPowers"
B = ZZ/101[x,y,z];
I = ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
isSymbPowerContainedinPower(I,3,2)
containmentProblem(I,2)
containmentProblemGivenSymbolicPower(I,4)     
isSymbPowerContainedinPower(I,4,3)


restart
loadPackage "SymbolicPowers"
R = QQ[x_1 .. x_(12)]
A = genericMatrix(R,3,4)
-- 3 x 3 minors
J = minors(3,A);
time symbolicPower(J,2) == J^2  -- used 3.59702 seconds
time isSymbolicEqualOrdinary(J,2) -- used 2.76583 seconds
-- 2 x 2 minors
I = minors(2,A);
time isSymbolicEqualOrdinary(I,2) -- 15 seconds
time symbolicPower(I,2) == I^2 -- used 63.6313 seconds




-- Examples with embedded primes
restart
loadPackage "SymbolicPowers"
R = QQ[x,y]
I = ideal"x2,xy"
I^2
symbolicPower(I,2)
symbolicPower(I,2, UseMinimalPrimes => true)


--Packing Problem
restart
loadPackage "SymbolicPowers"
R = QQ[x,y,z]
I = ideal(x*y,z*y,x*z)
isKonig(I)
--I is said to have the packing property if any ideal obtained 
--from I by setting any number of variables equal to 0 is Konig.
isPacked(I)
--Large example not packed  
restart
loadPackage "SymbolicPowers"
R = QQ[a,b,c,d,A,B,C,D]
J = ideal"ABCD,cdAB,abcD,bcABD,abcBD,abcdA,abcAD,abdAC,acdBC,acBCD,abcdC,bcdAC,bcACD,bcdAD,acdBD,adBCD,acABD,bdABC,adABC"
isPacked(J)
noPackedSub(J)
isPacked(J)
listofsub = noPackedAllSubs(J) -- slow
L = substitute(J,matrix{{1,0,c,d,A,1,C,D}})
isKonig(L)

