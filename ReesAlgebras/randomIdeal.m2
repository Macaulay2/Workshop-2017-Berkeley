newPackage(
    "randomIdeal",
    Version => "0.1",
    Date => "July 19, 2017",
    Authors => {{Name => "Lauren Cranton Heller",
	    Email => "lauren_heller@berkeley.edu"}},
    Headline => "my first Macaulay2 package",
    DebuggingMode => true
    )

needsPackage"SimpleDoc"
needsPackage"LocalRings"

export {"randomCombo"}

randomCombo=method(TypicalValue=>Ideal)
randomCombo(Ideal,ZZ) := (I,n) -> (
    L:=I_*;
    ideal apply(n,i->sum(L,j->random(coefficientRing ring I)*j))
)
randomCombo(List,ZZ) := (M,n) -> (
    L:=(ideal(M))_*;
    ideal apply(n,i->sum(L,j->random(coefficientRing ring ideal(M))*j))
)

export {"intersectIdeal"}

intersectIdeal=method(TypicalValue=>Ideal)
intersectIdeal(Ideal,ZZ) := (I,n) -> (
    R:=ring I;
    J:=ideal 0_R;
    while I!=J do (
	K:=randomCombo(I,n);
--	print K;
--	if K!=ideal 0_R then (
	    J=I;
	    I=intersect(I,K);
--	)
    );
    m := ideal gens R;
    G := flatten entries gens (I:m);
    d := 1 + max flatten for i in G list flatten degree i;
    J := I + m^d;
--    RP := localRing(R, m);
    K := ideal mingens J;
    K
)

beginDocumentation()
doc ///
    Key
    	randomIdeal
    Headline
    	generates and intersects random ideals
    Description
    	Text
 ///

end

restart
path = append(path,"~/Documents/Berkeley/Workshop-2017-Berkeley/ReesAlgebras/")
path = append(path,"~/Documents/Berkeley/Workshop-2017-Berkeley/ReesAlgebras/mahrud/")
loadPackage(Reload=>true,"randomIdeal")
R=ZZ/32003[x,y]
I=ideal{x^2,y,x*y^4}
intersectIdeal(I,2)
loadPackage "RandomIdeals"
