newPackage(
        "SpaceCurves",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "database of space curves and generation of such examples",
        DebuggingMode => true
        )

export {
    "AbstractSurface",	  --type
    "abstractSurface",	  --create an AbstractSurface
    "AbstractDivisor",	  --type
    "abstractDivisor",	  --create an AbstractDivisor	  
    "RealizedSurface",	  --type
    "RealizedDivisor",	  --type
    "realize",
    "abstractQuadric",
    "abstractCubic",
    "linesOnCubic",
    "abstractHypersurface",
    "abstractQuartic",
    "isIrreducible",
    "isSmooth",
    "CanonicalClass",
    "Hyperplane",
    "DivisorClass",
    "ExtraData",
    "IntersectionPairing",
    "dgTable",
    "hartshorneRaoModule",
    "hilbertBurchComputation",
    "minimalCurveInLiaisonClass",
    "Chi",
    "irreducibleDivisors",
    "completeIntersectionCurves"
    }


AbstractSurface = new Type of HashTable
-- Name,IntersectionPairing,Hyperplane,CanonicalClass,Chi
AbstractDivisor = new Type of HashTable
RealizedSurface = new Type of HashTable
-- AbstractSurface,Ideal,ExtraData
-- ExtraData for cubic: (Phi:P^2-->P^3, ideal of 6 Points)
RealizedDivisor = new Type of HashTable
-- AbstractDivisor, RealizedSurface, Ideal



--AbstractSurfaces--
ideal RealizedSurface := X -> X.Ideal
ideal RealizedDivisor := C -> C.Ideal

abstractSurface = method()
abstractSurface RealizedSurface := X -> X.AbstractSurface
abstractSurface AbstractDivisor := D -> D.AbstractSurface
abstractSurface List := data -> (
    -- data is a List containing all keys of the hashTable
    -- Name,IntersectionPairing,Hyperplane,CanonicalClass,Chi
    M := data#1;
    if numRows M != numColumns M then error "expected square matrix";
    -- TODO: add hodge index check.
    new AbstractSurface from {
	symbol Name => data#0,
        symbol IntersectionPairing => data#1,
        symbol Hyperplane => data#2,
        symbol CanonicalClass => data#3,
	symbol Chi => data#4
        }
    )

abstractQuadric = abstractSurface(
    {"Quadric surface",matrix{{0,1},{1,0}}, {1,1}, {-2,-2},1}
)
abstractCubic = abstractSurface(
    -- generators are L, -E1, ..., -E6
    {"Cubic surface",
    diagonalMatrix{1, -1, -1, -1, -1, -1, -1},
    {3,1,1,1,1,1,1}, 
    -{3,1,1,1,1,1,1},
    1}
)
linesOnCubic = () -> (
    Ds := apply(entries diagonalMatrix{1, -1, -1, -1, -1, -1, -1}, 
             d -> abstractDivisor(d,abstractCubic)
             );
    L := Ds#0;
    Es := drop(Ds,1);
    join(
        Es,
        for p in subsets(splice {1..6}, 2) list (
            L - Ds#(p#1) - Ds#(p#0)
            ),
        for i from 0 to 5 list (
            2*L - sum drop(Es, {i,i})
            )
        )
    )
abstractHypersurface = method()
abstractHypersurface ZZ := d -> abstractSurface(
	{"Hypersurface",
	 matrix{{d}},
	 {1},	 --Hyperplane class O(1) is denoted by 1
	 {-4+d}, --CanonicalClass is O(-d+4)
	 1+binomial(d-1,3)
	}
    )
abstractQuartic = method()
abstractQuartic String := Input -> (
    if Input == "line" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,1},{1,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "plane conic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,2},{2,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "twisted cubic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,3},{3,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "rational quartic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,4},{4,-2}},
	{1,0},
	{0,0},
	2});
    if Input == "plane elliptic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,3},{3,0}},
	{1,0},
	{0,0},
	2});
    if Input == "space elliptic" then return abstractSurface(
	 {"Quartic surface with a " | Input,
	matrix{{4,4},{4,0}},
	{1,0},
	{0,0},
	2});
    error "not implemented yet for your type of surface";
)

--AbstractDivisors--

abstractDivisor = method()
abstractDivisor(List, AbstractSurface) := (C, X) -> (
    new AbstractDivisor from {
        symbol DivisorClass => C,
        symbol AbstractSurface => X
        }
    )
net AbstractDivisor := D -> net D.DivisorClass
net AbstractSurface := X -> net X.Name
net RealizedSurface := X -> net X.Ideal
net RealizedDivisor := D -> net D.Ideal

ZZ * AbstractDivisor := (n,D) -> (
    abstractDivisor(n * D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor + AbstractDivisor := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    abstractDivisor(C.DivisorClass + D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor - AbstractDivisor := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    abstractDivisor(C.DivisorClass - D.DivisorClass, D.AbstractSurface)
    )
AbstractDivisor * AbstractDivisor := (C,D) -> (
    X := C.AbstractSurface;
    assert(X === D.AbstractSurface);
    assert(X.IntersectionPairing =!= null);
    (matrix{C.DivisorClass} * X.IntersectionPairing * transpose matrix{D.DivisorClass})_(0,0)
    )
AbstractDivisor == AbstractDivisor := (C,D) -> (
    C.AbstractSurface === D.AbstractSurface and C.DivisorClass == D.DivisorClass
    )

degree AbstractDivisor := C -> (
    X := C.AbstractSurface;
    return (matrix{C.DivisorClass} * X.IntersectionPairing * transpose matrix{X.Hyperplane})_(0,0);
    )
genus AbstractDivisor := C -> (
    X := C.AbstractSurface;
    K := abstractDivisor(X.CanonicalClass,X);
    return 1/2*((K+C)*C)+1;
    )
chi AbstractDivisor := C -> (
    X := C.AbstractSurface;
    K := abstractDivisor(X.CanonicalClass,X);
    1/2 * (C * (C-K)) + X.Chi
    )
degree RealizedDivisor := C -> degree ideal C
genus RealizedDivisor := C -> genus ideal C
chi RealizedDivisor := C -> null --to be added

--Smoothness and irreducibility--

isSmooth = method()
isSmooth Ideal := (I) -> (
    c := codim I;
    dim(I + minors(c, jacobian I)) == 0
    )
isSmooth RealizedSurface := X -> isSmooth ideal X
isSmooth RealizedDivisor := C -> isSmooth ideal C
isSmooth AbstractDivisor := C -> (
    if C.AbstractSurface.Name == "Quadric surface" then return isIrreducible C;
    if C.AbstractSurface.Name == "Cubic surface" then return isIrreducible C;
    if C.AbstractSurface.Name == "Hypersurface" then return true;
    error "Not implemented yet for this type of surface";  
)

isIrreducible = method()
isIrreducible AbstractDivisor := Boolean => C -> (
    --Checks whether a divisor class contains an irreducible curve
    X := C.AbstractSurface;
    if X.Name == "Cubic surface" then (
    	H := abstractDivisor(X.Hyperplane,X);
    	twentysevenLines := linesOnCubic();
    	return any(twentysevenLines, L -> L.DivisorClass == C.DivisorClass)
	or -- these are the conics:
    	any(twentysevenLines, L -> (H-L).DivisorClass == C.DivisorClass)
    	or (
     	    all(twentysevenLines, L -> L * C >= 0)
      	    and
     	    C*C > 0
     	);
    );
    if X.Name == "Quadric surface" then (
    	a := first C.DivisorClass;
	b := last C.DivisorClass;
	if a > 0 and b > 0 then return true;
	if a*b == 0 and a+b == 1 then return true;
	return false;	
    );
    error "Not implemented for your type of surface yet";
)
isIrreducible RealizedDivisor := Boolean => C -> isPrime ideal C 

--Realize--

realize = method(Options => {Ring => null, CoefficientRing => ZZ/32003})
realize AbstractSurface := opts -> X -> (
    -- Note: this is in P^3
    R := if opts#Ring =!= null then 
        opts#Ring 
      else (
        x := getSymbol "x";
        opts.CoefficientRing[x_0..x_3]
      );
    assert(numgens R == 4);
    kk := coefficientRing R;
    -- create the polynomial ring.
    if X.Name == "Cubic surface" then (
        y := getSymbol "y";
        S := kk(monoid[y_0..y_2]);
        RS := R ** S;
        while (
            M := diagonalMatrix({1,1,1}) | matrix{{1},{1},{1}} | random(S^3,S^2);
            points := apply(6,i-> ideal (vars S * syz transpose M_{i}));
            I := intersect points;
            fI := res I;
            phi := map(S,R,fI.dd_1);
            matS := sub(diff(transpose sub(vars S,RS),sub(vars R,RS) * sub(fI.dd_2,RS)),R);
            f := ideal det matS;
            -- now check that this is smooth
            --assert(ker phi == f);
            dim (f + ideal jacobian f) != 0
            ) do ();
        return new RealizedSurface from {
            symbol AbstractSurface => X,
            symbol Ideal => f, 
            symbol ExtraData => {phi, points}
            }
        );
    if X.Name == "Quadric surface" then (
        IQ := ideal(R_0*R_3-R_1*R_2);
        return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => IQ,
	    symbol ExtraData => {ideal(R_0,R_1),ideal(R_0,R_2)}
	    }
        );
    if X.Name == "Hypersurface" then (        
	return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => ideal random(4+first X.CanonicalClass,R),
	    symbol ExtraData => {}
	    }    	
    );
    if select("Quartic",X.Name) != {} then (
    	if select("line",X.Name) != {} then (
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal(random(3,R)*R_2+random(3,R)*R_3),
		symbol ExtraData => {ideal(R_2,R_3)}
      	    }     
	);	
    	if select("conic",X.Name) != {} then (
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal(random(3,R)*R_3+random(2,R)*(R_1^2-R_0*R_2)),
		symbol ExtraData => {ideal(R_3,R_1^2-R_0*R_2)}
      	    }     
	);
	if select("twisted cubic",X.Name) != {} then (
	    IT := minors(2,matrix{{R_0,R_1,R_2},{R_1,R_2,R_3}}),
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal ((gens IT)*random(R^3,R^{-2}))_(0,0),
		symbol ExtraData => {IT}
      	    }     
	);
	if select("rational quartic",X.Name) != {} then (
	    IR := monomialCurveIdeal(R,{1,3,4});
	    IQR := ideal (gens IR)*(transpose random(R^1,R^{-2,-3,-3,-3}))_(0,0),  
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => IQR,
		symbol ExtraData => {IR}
      	    }     
	);
    	if select("plane elliptic",X.Name) != {} then (
	    E := R_2*R_1^2-R_0^3+R_0*R_2^2;
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal (random(3,R)*R_3+random(1,R)*E),
		symbol ExtraData => {ideal(R_3,E)}
      	    }     
	);  
        if select("space elliptic",X.Name) != {} then (
	    Q := random(2,R);
	    return new RealizedSurface from {
	    	symbol AbstractSurface => X,
		symbol Ideal => ideal (random(2,R)*(R_0*R_3-R_1*R_2)+random(2,R)*Q),
		symbol ExtraData => {ideal(R_0*R_3-R_1*R_2,Q)}
      	    }     
	);    	
    );
    error "Not implemented yet";
    )

realize (AbstractDivisor,RealizedSurface) := opts -> (C, X) -> (
    if C.AbstractSurface =!= X.AbstractSurface then error "expected divisor class on the given surface";
    if X.AbstractSurface.Name == "Cubic surface" then (
        phi := X.ExtraData#0;
	pts := X.ExtraData#1;
        S := target phi;
        R := source phi;
        ab := C.DivisorClass;
        a := ab_0;
        ipts := trim intersect (for i from 1 to 6 list (pts_(i-1))^(ab_i));
        gipts := gens ipts;
        if min flatten degrees source gipts > a then return null else (
            cplane := ideal (gipts*random(source gipts,S^{-a}));
            SC := S/cplane;
            cspace := trim ker map(SC,R,phi.matrix);
            return new RealizedDivisor from {
		symbol AbstractDivisor => C,
		symbol RealizedSurface => X,
		symbol Ideal => cspace
		} ;
        )
    );
    if X.AbstractSurface.Name == "Quadric surface" then (
	RC := ring X.Ideal;
	kk := coefficientRing RC;
	z := getSymbol "z";
	cox := kk(monoid[z_0..z_3,Degrees=>{{0,1},{0,1},{1,0},{1,0}}]);
    	segre := {cox_0*cox_2,cox_0*cox_3,cox_1*cox_2,cox_1*cox_3};
	I := ideal random(C.DivisorClass,cox);
	if I == 0 then return null;
	segre = apply(segre, p -> sub(p,cox/I));
	return new RealizedDivisor from {
	    symbol AbstractDivisor => C,
	    symbol RealizedSurface => X,
	    symbol Ideal => kernel map(cox/I,RC,segre)
	};
    ); 
    if X.AbstractSurface.Name == "Hypersurface" then (
    	SP := ambient ring ideal X;
	f := sub((ideal X)_0,SP);
	return new RealizedDivisor from {
	    symbol AbstractDivisor => C,
	    symbol RealizedSurface => X,
	    symbol Ideal => ideal(random(first C.DivisorClass,SP),f)   
	};	
    );
    error "not implemented yet for your type of surface"
)
realize AbstractDivisor := opts -> C -> realize(C,realize(C.AbstractSurface))


--Rao Module--


minimalCurveInLiaisonClass=method()

minimalCurveInLiaisonClass(Ideal):= J-> (
    M := hartshorneRaoModule J;
    minimalCurveInLiaisonClass(M)
    )
    

minimalCurveInLiaisonClass(Module) := M -> (    
 -- a probalistic algorithm which over large finite fields will produce
 -- a minimal curve in the liaison class corresponding to M with high probability
    S := ring M; 
    assert(dim M ==0);  
    fM:= res(M,LengthLimit=>2); 
    --betti fM
    r:=rank fM_1-rank fM_0; -- rank of the 2nd syzygy module of M
    degs:=sort flatten degrees fM_2;
    degList:=unique subsets(degs,r-1);
    degList=sort apply(degList,c->(sum c,c))/last;
    apply(#degList,i->sum degList_i);
    i:=0;
    while (
	L:=-degList_i;
	G:=S^L;
	I:=hilbertBurchComputation(M,G);
	class I === class null)
        do (i=i+1);
    --betti I, L
    return I)

hilbertBurchComputation=method()
hilbertBurchComputation(Module,Module) := (M,G) -> (
    if not ring M === ring G then error "expected modules over the same polynomial ring";
    -- add check: isFree G == true
    fM:=res(M,LengthLimit=>2);
    if not 1+rank fM_0-rank fM_1 +rank G == 0 then error "the free module has the wrong rank";
    hom:=random(fM_2,G);
    hilbBurch := fM.dd_2*hom;
    degLim := -sum( -flatten degrees G) + sum(-flatten degrees fM_1)-sum(-flatten degrees fM_0);
    syzHilbBurch := syz(transpose hilbBurch,DegreeLimit=>degLim);
    ok := rank source syzHilbBurch == rank fM_0+1 and degrees source syzHilbBurch ==(-degrees fM_0|{{degLim}});
    if ok then return trim ideal(transpose syzHilbBurch_{ rank fM_0} * fM.dd_2) else return null)

hartshorneRaoModule=method()
hartshorneRaoModule(Ideal) := I -> (
    S:=ring I;
    d:= dim S;
    assert( dim I == 2);
    omega:=Ext^(d-2)(S^1/I,S^{-d});
    fomega := res omega;
    HRao := coker(Hom(fomega.dd_(d-2)_{0..(rank fomega_(d-2)-2)},S^{-d}));
    return HRao)

--Generation and Plotting--
dgTable = method()
dgTable List := L ->(
    --Takes a list of AbstractDivisors or RealizedDivisors
    --returns a (degree, genus)    
    Ldg := apply(L, C -> (lift(degree C,ZZ), lift(genus C,ZZ)));
    dmax := max apply(Ldg,dg->first dg);
    dmin := min apply(Ldg,dg->first dg);
    gmax := max apply(Ldg,dg->last dg);
    gmin := min apply(Ldg,dg->last dg);
    M := mutableMatrix map(ZZ^(gmax-gmin+1),ZZ^(dmax-dmin+1),0);
    for dg in Ldg do (
	j := first dg - dmin;
	i := gmax - last dg;
    	M_(i,j) = M_(i,j)+1;		
    );
    return matrix M;
)

irreducibleDivisors = method()
irreducibleDivisors (ZZ, AbstractSurface) := (d,X) -> (
    --List all irreducible abstract divisors of degree d on X
    if X.Name == "Cubic surface" then (
	return flatten for a from ceiling(d/3) to d list (
	    degreeList := apply(select(partitions(3*a-d),p->#p<=6),q ->
		{a} | toList q | splice{(6-#q):0});
	    --This gives unqiue representation up to change of 6 points
	    degreeList = select(degreeList, L -> L#0 >= L#1+L#2+L#3); 
	    divisorList := apply(degreeList, L-> abstractDivisor(L,X));
	    select(divisorList, D -> isIrreducible D)   
	);
    );
    if X.Name == "Quadric surface" then (
	maxdeg := floor(1/2*d);
	return for a from 1 to maxdeg list abstractDivisor({a,d - a},X);
    );
    if X.Name == "Hypersurface" then (
	surfd := 4 + first X.CanonicalClass;
	if d % surfd =!= 0 then return {};
	return abstractDivisor({d // surfd},X);
    );
    error "not implemented yet for your type of surface";	
)
irreducibleDivisors (ZZ, RealizedSurface) := (d,X) -> (
    --List all irreducible curves of degree d on X
   return apply(irreducibleDivisors(d,X.AbstractSurface), aD -> 
       realize(aD,X));	
)
completeIntersectionCurves  = method()
completeIntersectionCurves ZZ := d -> (
    --produce all ci curves of degree d
    div := for i from 2 to floor sqrt d when d % i == 0 list i;
    return apply(div, deg -> 
	abstractDivisor({d // deg},abstractHypersurface(deg)));            
)




beginDocumentation()
document { 
Key => SpaceCurves,
Headline => "Construction and Database of space curves",
"This package implements methods to collect data and examples of space curve",
PARA{},
SUBSECTION "Abstract surfaces and divisors",  
UL{   TO "AbstractSurface",	  --type      
      TO "AbstractDivisor",	  --type
      TO "abstractSurface",	  --create an AbstractSurface
      TO "abstractDivisor",	  --create an AbstractDivisor	   
      TO "abstractQuadric",
      TO "abstractCubic",
      TO "abstractHypersurface",
      TO "CanonicalClass",
      TO "Hyperplane",
      TO "DivisorClass",
      TO "ExtraData",
      TO "IntersectionPairing",
      TO "Chi",
      TO "isIrreducible",
      TO "isSmooth"
},
PARA{},
SUBSECTION "Realizations",  
UL{     TO "RealizedSurface",	  --type
        TO "RealizedDivisor",	  --type
        TO "realize"
},
PARA{},
SUBSECTION "Hartshorne-Rao module computations",  
UL{   TO "hartshorneRaoModule",
      TO "hilbertBurchComputation",
      TO "minimalCurveInLiaisonClass"
},
PARA{},
SUBSECTION "Collecting examples and information",  
UL{   TO "dgTable",
      TO "irreducibleDivisors",
      TO "completeIntersectionCurves"
}
}

doc ///
  Key
    abstractDivisor
    (abstractDivisor,List,AbstractSurface)
  Headline
    Creates an AbstractDivisor on an AbstractSurface   
  Usage
     C = abstractDivisor(L,X)
  Inputs
    L: List
       of coordinates of a divisor class in Num(X)
    X: Module
       an AbstractSurface
  Outputs
    C: AbstractDivisor
  Description
     Text
       Given a List of coordinates of a divisor class and an AbstractSurface X,
       creates an AbstractDivisor.  
     Example
       abstractDivisor({1,3},abstractQuadric)
       abstractDivisor({3,1,1,1,1,1,1},abstractCubic)
  SeeAlso
///

doc ///
    Key
      abstractHypersurface
      (abstractHypersurface, ZZ)
    Headline
      creates an AbstractSurface corresponding to a hypersurace	
    Usage
      X = abstractHypersurface(d)
    Inputs
      d: ZZ
        a degree
    Outputs
      X: AbstractSurface
    Description
    	Text
	  Creates a hypersurface of degree d of type AbstractSurface.
	Example
	  abstractHypersurface(4)
    SeeAlso
///

doc ///
  Key
    isSmooth
    (isSmooth, AbstractDivisor)
    (isSmooth, RealizedDivisor)
    (isSmooth, RealizedSurface)
    (isSmooth, Ideal)
  Headline
    checks whether a divisor or a surface is smooth  
  Usage
     B = isSmooth(C)
     B = isSmooth(X)
     B = isSmooth(I)
  Inputs
    C: AbstractDivisor
    C: RealizedDivisor
    X: RealizedSurface
    I: Ideal
  Outputs
    B: Boolean
  Description
     Text
       If the input is an AbstractDivisor, uses numerical criteria to determine 
       whether the divisor class contains an irreducible smooth curve.
       If the input is a RealizedDivisor or a RealizedSurface,
       checks if its ideal is smooth.
     Example
       X = abstractCubic
       C = abstractDivisor(X.Hyperplane,X)
       isSmooth C
       rC = realize C
       isSmooth rC
       isSmooth rC.RealizedSurface
  SeeAlso
///

doc ///
  Key
    isIrreducible
    (isIrreducible,AbstractDivisor)
    (isIrreducible,RealizedDivisor)
  Headline
    checks whether a divisor is irreducible  
  Usage
     B = isIrreducible(C)
  Inputs
    C: AbstractDivisor
    C: RealizedDivisor
  Outputs
    B: Boolean
  Description
     Text
       If the input is an AbstractDivisor, uses numerical criteria to determine 
       whether the divisor class contains an irreducible curve.
       If the input is a RealizedDivisor, checks if its ideal is prime.
     Example
       X = abstractCubic
       C = abstractDivisor(X.Hyperplane,X)
       isIrreducible C
       isIrreducible realize C
  SeeAlso
///


doc ///
    Key
    	realize
	(realize, AbstractSurface)
	(realize, AbstractDivisor, RealizedSurface)
	(realize, AbstractDivisor)
    Headline
    	realizes an AbstractSurface or an AbstractDivisor
    Usage
    	rX = realize(aX)
	rC = realize(aC,rX)
	rC = realize(aC)
    Inputs
    	aX: AbstractSurface
	aC: AbstractDivisor
	rX: RealizedSurface
    Outputs
    	rX: RealizedSurface
	rC: RealizedDivisor
    Description
    	Text
	    Constructs a RealizedSurface given an AbstractSurface. 
	    Constructs a RealizedDivisor given an AbstractDivisor 
	    on a RealizedSurface, if the RealizedSurface is not given,
	    then constructs the RealizedSurface first.
    	Example
	    R = ZZ/101[x_0..x_3]; aC = abstractDivisor({2,3},abstractQuadric);
	    aX = realize(abstractQuadric, Ring=>R)
	    realize(aC,aX);
	    realize(aC);
    SeeAlso    	      
///

doc ///
  Key
    hilbertBurchComputation
    (hilbertBurchComputation, Module, Module)
  Headline
    choose a Hilbert-Burch morphism and compute the corresponding ideal   
  Usage
     I = hilbertBurchComputation(M,G)
  Inputs
    M: Module
       of finite length
    G: Module
       a free module
  Outputs
     I: Ideal
  Description
     Text
       Let $\mathcal F$ be sheafication of the second syzygy module syz_2 M of M, phi be a randomly choosen
       morphism from G -> syz_2 M. The function computes the generators of the homogeneous ideal of coker phi.
       If rank G != rank $\mathcal F$-1 or the morpism does not drop rank in codimension 2, we return null. 
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker matrix{{x_0,x_1,x_2^2,x_3^2}}
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       degs=sort flatten degrees fM_2
       L=-{3,3}
       G=S^L
       I=hilbertBurchComputation(M,G)
       betti res I
       codim I == 2
       (degree I,genus I) == (4,-1) 
       cI=decompose I     
       tally apply(cI,c->(degree c, genus c))
       I=hilbertBurchComputation(M,S^2)
       I==null
  SeeAlso
///

doc ///
  Key
    hartshorneRaoModule
    (hartshorneRaoModule, Ideal)
  Headline
    compute the Hartshorne-Rao module    
  Usage
     M = hartshorneRaoModule I
  Inputs
    I: Ideal
       of a (locally) Cohen-Macaulay curve
  Outputs
     M: Module
  Description
     Text
       Given I the homogeneous ideal of a (locally) Cohen-Macaulay curve in some projective space P^n, th function computes
       the Hartshorne-Rao module
       $$ M = \oplus H^1(P^r,\mathcal I(n)).$$  
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker random(S^{2:1},S^{5:0})
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       F=fM_2
       degs=sort flatten degrees F
       L=-degs_{0..r-2}
       G=S^L
       I=hilbertBurchComputation(M,G)
       betti I
       HRao = hartshorneRaoModule(I); betti HRao        
       reduceHilbert hilbertSeries HRao === reduceHilbert hilbertSeries (M**S^{ -2})
  SeeAlso
///

doc ///
  Key
    minimalCurveInLiaisonClass
    ( minimalCurveInLiaisonClass, Module)
    ( minimalCurveInLiaisonClass, Ideal)
  Headline
    probabilistic computation of a minimal curve in the even liaison class   
  Usage
     I = minimalCurveInLiaisonClass M
     I = minimalCurveInLiaisonClass J
  Inputs
    M: Module
       a given Hartshorne-Rao module, or
    J: Ideal
       of a CM curve in P^3
  Outputs
    I: Ideal
        of a locally CM curve in P^3
  Description
     Text
       Given M we compute a (locally) Cohen-Macaulay curve P^3 in the even liaison class represented by M
       (of the curve defined by J).
       The algorithm is only probalistic, i.e. with bad luck we might miss the minimal class due to the eandom choice for the Hilbert-Burch morphism.        
     Example
       S = ZZ/32003[x_0..x_3]
       M=coker matrix{{x_0,x_1,x_2^2,x_3^2}}
       dim M
       reduceHilbert hilbertSeries M
       betti(fM=res M)
       r=rank fM_1-rank fM_0
       degs=sort flatten degrees fM_2
       L=-{3,3}
       G=S^L
       J=hilbertBurchComputation(M,G)
       M=hartshorneRaoModule J
       I=minimalCurveInLiaisonClass M
       degree I, degree J
  SeeAlso
///

doc ///
  Key
    irreducibleDivisors
    (irreducibleDivisors, ZZ, AbstractSurface)
    (irreducibleDivisors, ZZ, RealizedSurface)
  Headline
    creates irreducible divisors of a fixed degree on a given surface   
  Usage
     L = irreducibleDivisors(d,X)
  Inputs
    d: ZZ
       a degree
    X: AbstractSurface
    X: RealizedSurface
  Outputs
    L: List
        of AbstractDivisors or RealizedDivisors of degree d on X 
  Description
     Text
       Produces all irreducible divisors of degree d on a given surface X.
       If X is an AbstractSurface, returns a list of AbstractDivisors.
       if X is a RealizedSurface, returns a list of RealizedDivisors.          
     Example
       S = ZZ/32003[x_0..x_3]
       irreducibleDivisors(4,abstractCubic)
       irreducibleDivisors(4,realize(abstractCubic, Ring=> S))
  SeeAlso
      completeIntersectionCurves
///

doc ///
  Key
    completeIntersectionCurves
    (completeIntersectionCurves, ZZ)
  Headline
    creates all complete intersection curves of a fixed degree in P^3   
  Usage
     L = completeIntersectionCurves(d)
  Inputs
    d: ZZ
       a degree
  Outputs
    L: List
        of AbstractDivisors on hypersurfaces
  Description
     Text
       Produces all degree d complete intersection curves in P^3. 
       The list consists of divisors of degree a on hypersurfaces of degree b
       where b <= a and a*b = d.          
     Example
       completeIntersectionCurves(4)
  SeeAlso
///

doc ///
  Key
    dgTable
    (dgTable, List)
  Headline
    records occurancecs of (degree,genus) pair from a list of divisors   
  Usage
    M = dgTable(L)
  Inputs
    L: List
       of AbstractDivisors or RealizedDivisors
  Outputs
    M: Matrix
        of occurencies of a (degree,genus) pair 
  Description
     Text
       Produces from a list of divisors an occurence matrix, 
       the rows are indexed by genus and the columns by degree.          
     Example
       R = ZZ/101[x_0..x_3];
       L = flatten apply({2,3,4}, d->irreducibleDivisors(d,abstractQuadric));
       dgTable L
       dgTable (L / realize)   
  SeeAlso
///
--TEST SECTION

TEST ///
  X = abstractQuadric
  R = QQ[a,b]
  C = abstractDivisor({a,b},X)
  degree C
  genus C
  chi C
///

TEST ///
  X = abstractCubic
  R = QQ[a,b_1..b_6]
  C = abstractDivisor(gens R,X)
  degree C
  genus C
  chi C
///

TEST ///
  S = ZZ/32003[a..d]
  X = realize(abstractCubic, Ring => S)
  C = abstractDivisor({3,1,1,1,0,0,0},abstractCubic)
  isIrreducible C
  assert(degree C == 6)
  assert(genus C == 1)
  I = realize(C,X)
  isSmooth I
  betti res ideal I
  assert(degree I == degree C)
  assert(genus I == genus C)
///

TEST ///
  S = ZZ/32003[a..d]
  X = realize(abstractCubic, Ring => S)
  C = abstractDivisor({2,1,1,1,0,0,0},abstractCubic)
  isIrreducible C
  (degree C, genus C)
  rC = realize(C,X)
  betti ideal rC
  isSmooth rC
  betti res ideal rC
  assert(degree rC == degree C)
  assert(genus rC == genus C)
///

TEST ///
    S = ZZ/101[x_0..x_3];
    X = realize(abstractHypersurface(3), Ring => S)
    C = abstractDivisor({4},X.AbstractSurface)
    degree C
    genus C
    rC = realize(C,X)
    assert(degree rC == degree C);
    assert(genus rC == genus C);
///


TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker random(S^{2:1},S^{5:0})
  dim M
  reduceHilbert hilbertSeries M
  betti(fM=res M)
  r=rank fM_1-rank fM_0
  F= fM_2
  degs=sort flatten degrees F
  L=-degs_{0..r-2}
  G=S^L
  I=hilbertBurchComputation(M,G)
  betti I
  assert( codim I == 2)
  assert((degree I,genus I) == (7,2))
--I=hilbertBurchComputation(M,S^3)
  I=hilbertBurchComputation(M,S^2)
  I==null
///

TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker (koszul(2,vars S)|random(S^{4:-1},S^{4:-3}));
  betti M
  dim M == 0
  time I=minimalCurveInLiaisonClass M; -- used 0.58667 seconds
  assert( (degree I, genus I) == (43, 168) )
{*
  omega=Ext^2(S^1/I,S^{-4});
  fomega=res omega
  betti fomega
  HRao= coker(Hom(fomega.dd_2_{0..(rank fomega_2-2)},S^{-4}))
  reduceHilbert hilbertSeries HRao
  reduceHilbert hilbertSeries M
*}
///	


TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker random(S^{2:1},S^{5:0})
  dim M
  reduceHilbert hilbertSeries M
  betti(fM=res M)
  r=rank fM_1-rank fM_0
  F= fM_2
  degs=sort flatten degrees F
  L=-degs_{0..r-2}
  G=S^L
  I=hilbertBurchComputation(M,G)
  betti I
  HRao = hartshorneRaoModule(I)        
  assert(reduceHilbert hilbertSeries HRao === reduceHilbert hilbertSeries (M**S^{ -2}))
///


end--
restart
uninstallPackage "SpaceCurves"
restart
installPackage "SpaceCurves"
viewHelp "SpaceCurves"



--Generate all divisors of degree d
restart
needsPackage "SpaceCurves"
check "SpaceCurves"

dmax = 12
--AbstractDivisors
time adList = flatten apply(dmax, d-> 	  -- used 8.09871 seconds
    irreducibleDivisors(d+1,abstractQuadric) |
    irreducibleDivisors(d+1,abstractCubic)   |
    completeIntersectionCurves(d+1)	
    );
--RealizedDivisors
x = getSymbol "x";
R = ZZ/101[x_0..x_3]	  
time rdList = flatten apply(dmax, d-> 	-- used 10.9523 seconds
    irreducibleDivisors(d+1,realize(abstractQuadric,Ring => R)) |
    irreducibleDivisors(d+1,realize(abstractCubic,Ring=>R))   |
    apply(completeIntersectionCurves(d+1), ci->realize(ci,Ring=>R))	
    );	  
dgTable adList, dgTable rdList
