-- -*- coding: utf-8-unix -*-
-- Code for Simplicial Complexes Extras

--------------------------------------------------------------------------------
-- Copyright 2017  Jason McCullough
-- 
-- You may redistribute this program under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2 of the
-- License, or any later version.
--------------------------------------------------------------------------------

-- Janko added class Face to be used in other packages
-- should not affect the functionality present previously

newPackage(
	"SimplicialComplexesTemp",  -- MERGE ME number 2
    	Version => "1.0", 
    	Date => "July 19, 2017",
    	Authors => {
	     {Name => "Jason McCullough", Email => "jmccullo@iastate.edu", HomePage => "http://users.rider.edu/~jmccullough"}
	     },
    	Headline => "simplicial complexes add-ons",
    	DebuggingMode => false,
	PackageExports=>{ "SimplicialComplexes"}
    	)


export {"simplicialJoin","poincareSphere","dunceHat","suspension","projectivePlane",
    "bjornerExample"}

-- Jason's area to work in

poincareSphere = method(Options=>{Variable => "x"})
poincareSphere(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_16];
    L := {{1,2,4,9},
	{1,2,4,15},
	{1,2,6,14},
	{1,2,6,15},
	{1,2,9,14},
	{1,3,4,12},
	{1,3,4,15},
	{1,3,7,10},
	{1,3,7,12},
	{1,3,10,15},
	{1,4,9,12},
	{1,5,6,13},
	{1,5,6,14},
	{1,5,8,11},
	{1,5,8,13},
	{1,5,11,14},
	{1,6,13,15},
	{1,7,8,10},
	{1,7,8,11},
	{1,7,11,12},
	{1,8,10,13},
	{1,9,11,12},
	{1,9,11,14},
	{1,10,13,15},
	{2,3,5,10},
	{2,3,5,11},
	{2,3,7,10},
	{2,3,7,13},
	{2,3,11,13},
	{2,4,9,13},
	{2,4,11,13},
	{2,4,11,15},
	{2,5,8,11},
	{2,5,8,12},
	{2,5,10,12},
	{2,6,10,12},
	{2,6,10,14},
	{2,6,12,15},
	{2,7,9,13},
	{2,7,9,14},
	{2,7,10,14},
	{2,8,11,15},
	{2,8,12,15},
	{3,4,5,14},
	{3,4,5,15},
	{3,4,12,14},
	{3,5,10,15},
	{3,5,11,14},
	{3,7,12,13},
	{3,11,13,14},
	{3,12,13,14},
	{4,5,6,7},
	{4,5,6,14},
	{4,5,7,15},
	{4,6,7,11},
	{4,6,10,11},
	{4,6,10,14},
	{4,7,11,15},
	{4,8,9,12},
	{4,8,9,13},
	{4,8,10,13},
	{4,8,10,14},
	{4,8,12,14},
	{4,10,11,13},
	{5,6,7,13},
	{5,7,9,13},
	{5,7,9,15},
	{5,8,9,12},
	{5,8,9,13},
	{5,9,10,12},
	{5,9,10,15},
	{6,7,11,12},
	{6,7,12,13},
	{6,10,11,12},
	{6,12,13,15},
	{7,8,10,14},
	{7,8,11,15},
	{7,8,14,15},
	{7,9,14,15},
	{8,12,14,15},
	{9,10,11,12},
	{9,10,11,16},
	{9,10,15,16},
	{9,11,14,16},
	{9,14,15,16},
	{10,11,13,16},
	{10,13,15,16},
	{11,13,14,16},
	{12,13,14,15},
	{13,14,15,16}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)

dunceHat = method(Options=>{Variable => "x"})
dunceHat(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_8];
    L := {{1,2,4},
{1,2,7},
{1,2,8},
{1,3,4},
{1,3,5},
{1,3,6},
{1,5,6},
{1,7,8},
{2,3,5},
{2,3,7},
{2,3,8},
{2,4,5},
{3,4,8},
{3,6,7},
{4,5,6},
{4,6,8},
{6,7,8}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)

projectivePlane = method(Options=>{Variable => "x"})
projectivePlane(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_6];
    L := {{1,2,4},
{1,2,6},
{1,3,4},
{1,3,5},
{1,5,6},
{2,3,5},
{2,3,6},
{2,4,5},
{3,4,6},
{4,5,6}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)


bjornerExample = method(Options=>{Variable => "x"})
bjornerExample(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_6];
    L := {{1,2,3},
{1,2,5},
{1,2,6},
{1,3,4},
{1,3,6},
{1,4,5},
{2,3,4},
{2,3,5},
{2,4,6},
{3,5,6},
{4,5,6}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)

-- end Jason's work area

-- Claudiu's work area

--experts say that we only need | for joining simplicial complexes

externalJoin = method()
externalJoin(SimplicialComplex,SimplicialComplex) := (S1,S2) -> (
    R1 := ring S1;
    R2 := ring S2;
    if R1 === R2 then internalJoin(S1,S2) else
    (
	R := R1 ** R2;
	n1 := numgens R1;
	n2 := numgens R2;
	i1 := map(R,R1,apply(n1,j -> R_j));
	i2 := map(R,R2,apply(n2,j -> R_(n1+j)));
	newS1 := simplicialComplex apply(flatten entries facets S1,f -> i1(f));
	newS2 := simplicialComplex apply(flatten entries facets S2,f -> i2(f));
	internalJoin(newS1,newS2)
	)
    )

internalJoin = method()
internalJoin(SimplicialComplex,SimplicialComplex) := (S1,S2) ->
(
    fS1 := flatten entries facets(S1);
    fS2 := flatten entries facets(S2);
    simplicialComplex(flatten for f1 in fS1 list for f2 in fS2 list lcm(f1,f2))
    ) 


SimplicialComplex | SimplicialComplex := (S1,S2) -> externalJoin(S1,S2)

cone(SimplicialComplex) := (S) -> (
    R := ring S;
    k := coefficientRing R;
    Q := k(monoid[getSymbol "X"]);
    point := simplicialComplex {Q_0};
    S | point
    )


suspension = method()
suspension(SimplicialComplex):= (S)-> (
    R := ring S;
    k := coefficientRing R;
    Q := k(monoid[getSymbol "X", getSymbol "Y"]);  
    points := simplicialComplex{Q_0,Q_1};
    S | points
    )

end


----Claudiu's Test Area
restart
installPackage"SimplicialComplexesTemp"

r1 = QQ[a,b]
s1 = simplicialComplex {a,b}
r2 = QQ[a,c]
s2 = simplicialComplex {a,c}
s1 | s2

cone(s1)
suspension(s2)

-----


------bug?-----
restart
R1 = QQ[a]
R2 = QQ[a]
R = R1 ** R2
dim R
i1 = map(R,R1)
i2 = map(R,R2)
i1(R1_0) - i2(R2_0)


n1 = numgens R1
n2 = numgens R2
i1 = map(R,R1,apply(n1,j -> R_j))
i2 = map(R,R2,apply(n2,j -> R_(n1+j)))
i1(R1_0) - i2(R2_0)

----end Claudiu's Test Area


-- Jason test area --

restart
F = ZZ/2
loadPackage "SimplicialComplexesTemp"
S = poincareSphere(F,Variable => x)
T = dunceHat(F,Variable => y)
U = projectivePlane(F,Variable =>z)
V = bjornerExample(F)
zero HH_(-1) V
zero HH_0 V
zero HH_1 V
zero HH_2 V
zero HH_3 V
fVector V
transpose facets V
prune HH_2(chainComplex U)
-- end Jason test area


