newPackage(
    "RandomIdeal",
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
randomCombo(Ideal) := I -> (
    L:=I_*;
    R:=ring I;
    n:=#(gens R);
    ideal apply(n,i->sum(L,j->random(coefficientRing R)*j))
)
randomCombo(List) := M -> (
    I:=ideal(M);
    L:=I_*;
    R:=ring I;
    n:=#(gens R);
    ideal apply(n,i->sum(L,j->random(coefficientRing R)*j))
)

export {"intersectSteps"}

intersectSteps=method(TypicalValue=>ZZ)
intersectSteps(Ideal) := I -> (
    R:=ring I;
    n:=#(gens R);
    I=ideal gens gb I;
    J:=I;
    K:=ideal 1_R;
    c:=0;
    while (J:K)!=(ideal 1_R) do (
	c=c+1;
	K=J;
	J=ideal gens gb intersect(K,randomCombo(I));
    	--G := flatten entries gens (I:(ideal gens R));
    	--d := 1 + max flatten for i in G list flatten degree i;
    	--ideal gens gb (I+m^d);
    );
    c-1
)

export {"intersectIdeal"}

intersectIdeal=method(TypicalValue=>Ideal)
intersectIdeal(Ideal) := I -> (
    R:=ring I;
    n:=#(gens R);
    I=ideal gens gb I;
    J:=I;
    K:=ideal 1_R;
    while (J:K)!=(ideal 1_R) do (
	K=J;
	J=intersect(K,randomCombo(I));
    );
    m := ideal gens R;
    G := flatten entries gens (J:(ideal gens R));
    d := 1 + max flatten for i in G list flatten degree i;
    ideal gens gb (J+m^d)
)

beginDocumentation()
doc ///
    Key
        RandomIdeal
    Headline
    	generates and intersects random ideals
    Description
    	Text
 ///

end

restart
path = append(path,"~/Documents/Berkeley/Workshop-2017-Berkeley/ReesAlgebras/")
path = append(path,"~/Documents/Berkeley/Workshop-2017-Berkeley/ReesAlgebras/mahrud/")
loadPackage(Reload=>true,"RandomIdeal")
loadPackage(Reload=>true,"RandomIdeals")

R=ZZ/32003[x,y]
for i from 1 to 12 list (
    I=(ideal{x,y})^i;
    c=intersectSteps(I)
)

tally for i from 0 to 9 list (
    print i;
    R=ZZ/32003[x_{0}..x_{2}];
    I=randomMonomialIdeal(apply(1+random(5),j->1+random(5)),R)
        +ideal(apply(#(gens R),j->x_{j}^(1+random(5))));
    print I;
    intersectSteps(I)
)
