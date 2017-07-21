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


export {"simplicialJoin","poincareSphere","dunceHat","suspension",
    "projectivePlane","bjornerExample","hachimoriExample1",
    "hachimoriExample2","hachimoriExample3","hachimoriExample4","ringMap",
    "simplicialComplexMap","SimplicialComplexMap","composition","skeleton"}

-- Jason's area to work in

-- New Type to keep track of simplicial maps
SimplicialComplexMap = new Type of HashTable
simplicialComplexMap = method(TypicalValue => SimplicialComplexMap)

-- Internal simplicial map constructor
newSimplicialComplexMap := (T,S,f) ->
     new SimplicialComplexMap from {
	  symbol target => T,
	  symbol source => S,
	  ringMap => f,
	  symbol cache => new CacheTable
	  }

-- How to make a new simplicial map with some error checking
simplicialComplexMap (SimplicialComplex,SimplicialComplex,RingMap) := (T,S,f) -> (
    RT := ring T;
    RS := ring S;
    if not RT === target f 
    then error "target complex's ring does not match target of ring map";
    if not RS === source f 
    then error "source complex's ring does not match source of ring map";

    facetsT := apply(flatten entries facets T,fc->face(fc));
    imageOfFacetsS := apply(flatten entries facets S,fc->face(f(fc)));
    if not all(imageOfFacetsS,fs->(any(facetsT,ft->isSubface(fs,ft))))
    then error "Given ring map does not induce a simplicial map";
    
    newSimplicialComplexMap(T,S,f)
    )

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


hachimoriExample1 = method(Options=>{Variable => "x"})
hachimoriExample1(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_7];
    L := {{1,2,5},
{1,2,6},
{1,2,7},
{1,3,4},
{1,4,5},
{1,6,7},
{2,3,4},
{2,3,5},
{2,3,6},
{2,4,7},
{3,5,6},
{4,5,7},
{5,6,7}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)


hachimoriExample2 = method(Options=>{Variable => "x"})
hachimoriExample2(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_12];
    L := {{1,2,5},
{1,2,6},
{1,2,7},
{1,3,4},
{1,3,9},
{1,4,5},
{1,6,7},
{1,8,10},
{1,8,11},
{1,8,12},
{1,9,10},
{1,11,12},
{2,3,4},
{2,3,5},
{2,3,6},
{2,4,7},
{3,5,6},
{3,8,9},
{3,8,10},
{3,8,11},
{3,10,11},
{4,5,7},
{5,6,7},
{8,9,12},
{9,10,12},
{10,11,12}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)


hachimoriExample3 = method(Options=>{Variable => "x"})
hachimoriExample3(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_12];
    L := {{1,2,5},
{1,2,6},
{1,2,7},
{1,3,4},
{1,3,9},
{1,4,5},
{1,6,7},
{1,8,10},
{1,8,11},
{1,8,12},
{1,9,10},
{1,11,12},
{2,3,4},
{2,3,5},
{2,3,6},
{2,4,7},
{3,5,6},
{3,8,9},
{3,8,10},
{3,8,11},
{3,10,11},
{4,5,7},
{5,6,7},
{8,9,12},
{9,10,12},
{10,11,12}};
    fac := apply(L,l->product apply(l,v->R_(v-1)));
    simplicialComplex fac)



hachimoriExample4 = method(Options=>{Variable => "x"})
hachimoriExample4(Ring) := SimplicialComplex => o -> (F) -> (
    assert(isField F);
    x := o.Variable;
    if instance(x,String) then x = getSymbol x;
    R := F[x_1..x_12];
    L := {{1,2,5},
{1,2,6},
{1,2,7},
{1,3,4},
{1,3,9},
{1,4,5},
{1,6,7},
{1,8,10},
{1,8,11},
{1,8,12},
{1,9,10},
{1,11,12},
{2,3,4},
{2,3,5},
{2,3,6},
{2,4,7},
{3,5,6},
{3,8,9},
{3,8,10},
{3,8,11},
{3,10,11},
{4,5,7},
{5,6,7},
{8,9,12},
{9,10,12},
{10,11,12}};
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
---internal join of simplical complexes
--given two simplicial complexes S1,S2, the internal join
--computes the simplicical complex whose faces are the unions of
--faces of S1 and S2
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




composition = method()
composition(SimplicialComplex, List) := (K,L)-> (
    RK := ring K ;
    m := numgens(RK); ---m is the size of the underlying set of the simplicial complex K
    R := apply(L, i->ring i);
    N := apply(R,i->numgens i);
    aux := R#0;
    for i from 1 to #R-1 do aux=aux**R#i ;
    Q := aux;
    ind := 0;
    inc := for i from 0 to #R-1 list (
    	I := apply(N#i, t->Q_(ind + t));
    	ind=ind + N#i;
    	map(Q,R#i, I  )
    	);
    listFacetsK := flatten entries facets(K);
    simplicialComplex flatten for monF in listFacetsK list(
    	F := {}; ---F is the index set of the facet of K corresponding to the monomial monF
    	FC := {}; ---FC is the complement of F in {1,...,m}
    	for i from 0 to m-1 do(
    	    if monF%RK_i==0 then F=F|{i} 
    	    else FC=FC|{i};
        );
        prodOverF := product for i in F list (inc#i)(product(gens(R#i)));
	---prodOverF is the product of the simplices corresponding to the 
	---simplicial complexes indexed by elements of F
        auxset := set{infinity};
    	for i in FC do(
    	    set2 := set( flatten entries inc#i(facets(L#i)) );
    	    auxset=auxset**set2;    
    	    );
    	tupfacets := toList auxset;
    	for tup in tupfacets list(
    	    auxtup := tup;
    	    partialfacet := product while auxtup =!= infinity list (
	    	auxfct := auxtup_1; auxtup = auxtup_0;auxfct);
    	    partialfacet*prodOverF    
    	    )
	)
)




skeleton = method()
skeleton(ZZ,SimplicialComplex) := (n,S)->(
    F := flatten entries faces(n,S);  
    R := ring S;
    if F == {} then simplicialComplex {0_R} else simplicialComplex F
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
S = dunceHat(F,Variable => y)
T = projectivePlane(F)
RS = ring S
RT = ring T
f = map(RS,RS)
simplicialComplexMap(S,S,f)
g = map(RT,RS,(toList(x_1..x_6)|{x_1,x_1}))
simplicialComplexMap(T,S,g)


zero HH_(-1) V
zero HH_0 V
zero HH_1 V
zero HH_2 V
zero HH_3 V
fVector V
transpose facets V
prune HH_2(chainComplex U)
S = poincareSphere(F,Variable => x)
T = dunceHat(F,Variable => y)
zero HH_1 S
zero HH_2 S
prune HH_3 S


-- end Jason test area


R = QQ[x,y,z]

factor(x*y*z)
index(y)
methods map
code (map, Ring, Ring, Matrix)

methods RingMap

------Josh test area


---composition
restart
loadPackage "SimplicialComplexesTemp"
R=QQ[x_1,x_2,x_3,x_4]
R1=QQ[a,b,c,d]
R2=QQ[e,f,g]
K=simplicialComplex {x_1,x_2,x_3*x_4}
L1=simplicialComplex {a*b,b*d,d*c,a*c}
L2=simplicialComplex {e*f,f*g}
L={L1,L2,L2,L2}

composition(K,L)




-----------composition examples1
R=QQ[x,y,z]
O=QQ[o]
o1=simplicialComplex(monomialIdeal flatten entries vars O)
o1 = simplicialComplex{1_O}
K=simplicialComplex {x,y*z}
composition(K,splice{3:o1})
composition(o1,{K})


-----------composition examples2


o = getSymbol"o"
O=QQ[o_1..o_2]
R1=QQ[a,b]
R2=QQ[c,d]
S1=simplicialComplex {a,b}
S2=simplicialComplex {c,d}
o2= simplicialComplex{1_O}
composition(o2,{S1,S2})
S1|S2




--------n-skeleton examples


restart
loadPackage "SimplicialComplexesTemp"
R=QQ[x_1,x_2,x_3,x_4]
R1=QQ[a,b,c,d]
R2=QQ[e,f,g]
K=simplicialComplex {x_1,x_2,x_3*x_4}
faces(1,K)
faces(0,K)

skeleton(1,K)

skeleton(0,K)
skeleton(5,K)
skeleton(-1,K)
skeleton(-2,K)



------testing skeleton function for void complex
V=simplicialComplex{0_R}
skeleton(-1,V)
skeleton(0,V)
skeleton(2,V)


-------testing skeleton function for empty set complex
T=simplicialComplex{1_R}
skeleton(-1,T)
skeleton(0,T)








-------

R=QQ[a,b,c,d]
viewHelp gcd 
gcd{a*b,b*c,c*d}
time gcd{a*b,b*c,a*c,a*d,b*d,c*d}
time gcd{a^3*b,b^5*c^3,c*d^4,a^5*c^6}
time product{set{a,b},set{b,c},set{a,c},set{a,d},set{b,d},set{c,d}}
time product apply(subsets(50,4), l->set l)
S = QQ[x_0..x_49]
mons = apply(subsets(50,4), l->product apply(l,i->x_i));
time gcd mons



-----
restart
loadPackage "SimplicialComplexesTemp"
S=projectivePlane(QQ)
R=ring S;
n=dim R;
monF=flatten entries facets(S)
F=for monL in monF list(
    L := {};
    for i from 0 to n-1 do(
    	    if monL%R_i==0 then L=L|{i} 
        );
    set L
)
m=#F
kk=coefficientRing R;
x=getSymbol "x"
Q=kk[x_0..x_(m-1)]
--HT=new MutableHashTable from {}
nerveFacets={}
nerve=method()
nerve(List) := L-> (
    print L;
    --if not HT#?L then (
	k := max(L | {-1});
	facet := true;
	for i from k+1 to m-1 do(
	    newL := L|{i};
	    intersection := product apply(newL,j->F#j);
	    if intersection=!=set{} then (
		facet=false;
		nerve(newL);
		);
            );
	if facet then (
	    nerveFacets=nerveFacets|{product apply(L,j->Q_j)};
	    --for U in subsets(L) do HT#U=1;
	    );
-- );
);
nerve{}
nerveFacets

S=simplicialComplex nerveFacets
isPure(S)
fVector(S)
------nerve 
R=QQ[x_0..x_3]
S=simplicialComplex monomialIdeal(x_0*x_1*x_2,x_0*x_1*x_3,x_0*x_2*x_3)
