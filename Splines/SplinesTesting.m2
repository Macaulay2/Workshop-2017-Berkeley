--fixing bug in cellularComplex to make sure complex has the correct length--
restart
installPackage("AlgebraicSplines",FileName=>"~/Documents/Macaulay2/SplineCode/Workshop-2017-Berkeley/Splines/AlgebraicSplines.m2")
V={{0,0,0},{1,0,0},{0,1,0},{0,0,1},{-1,0,0},{0,-1,0},{0,0,-1}};
F={{0,1,2,3},{0,1,2,6},{0,2,3,4},{0,2,4,6}};
F={{0,1,2,3},{0,1,2,4}}
getCodim1Intersections(F,InputType=>"Simplicial")
cellularComplex(V,F)
splineModule(V,F,1)
splineMatrix(V,F,1)

--polyhedral example--
restart
uninstallPackage "AlgebraicSplines"
installPackage("AlgebraicSplines",FileName=>"~/Documents/Macaulay2/SplineCode/Workshop-2017-Berkeley/Splines/AlgebraicSplines.m2")
check "AlgebraicSplines"
V={{0,0,0},{1,1,1},{-1,1,1},{-1,1,-1},{1,1,-1},{1,-1,1},{-1,-1,1},{-1,-1,-1},{1,-1,-1}};
F={{0,1,2,3,4},{0,1,4,5,8}}
F={{0,1,2,3,4},{0,1,4,5,8},{0,5,6,7,8},{0,2,3,6,7},{0,1,2,5,6}}
S=QQ[x,y,z,w]
cellularComplex(V,F,BaseRing=>S)
splineComplex(V,F,0,BaseRing=>S)
idealsComplex(V,F,0,BaseRing=>S)
