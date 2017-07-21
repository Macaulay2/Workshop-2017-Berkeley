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
    "isSmooth",
    "AbstractSurface",	  --type
    "abstractSurface",	  --create an AbstractSurface
    "AbstractDivisor",	  --type
    "abstractDivisor",	  --create an AbstractDivisor	  
    "RealizedSurface",	  --type
    "RealizedDivisor",	  --type
    "realize",
    "abstractQuadric",
    "abstractCubic",
    "abstractHypersurface",
    "irreducibleOnCubic",
    "Chi",
    "CanonicalClass",
    "Hyperplane",
    "DivisorClass",
    "ExtraData",
    "IntersectionPairing",
    "effectiveDivisors",
    "dgTable",
    "hartshorneRaoModule",
    "hilbertBurchComputation",
    "minimalCurveInLiaisonClass"
    }


AbstractSurface = new Type of HashTable
-- IntersectionMatrix
-- Hyperplane
-- CanonicalClass
-- Chi
AbstractDivisor = new Type of HashTable
-- AbstractSurface
-- DivisorClass
RealizedSurface = new Type of HashTable
-- AbstractSurface
-- Ideal
-- ExtraData
-- e.g. For cubic: (Phi:P^2-->P^3, ideal of 6 Points)
RealizedDivisor = new Type of HashTable
-- AbstractDivisor
-- RealizedSurface
-- Ideal

ideal RealizedSurface := X -> X.Ideal
ideal RealizedDivisor := C -> C.Ideal

--AbstractSurfaces--

abstractSurface = method()
abstractSurface RealizedSurface := X -> X.AbstractSurface
abstractSurface AbstractDivisor := D -> D.AbstractSurface
abstractSurface(Matrix, List, List, ZZ) := (M, hyperplane, canonical, surfaceChi) -> (
    -- M is integer matrix of intersection pairing of Num(X)
    rho := numRows M;
    if rho != numColumns M then error "expected square matrix";
    -- TODO: add hodge index.
    new AbstractSurface from {
        symbol IntersectionPairing => M,
        symbol Hyperplane => hyperplane,
        symbol CanonicalClass => canonical,
        symbol Chi => surfaceChi
        }
    )

abstractQuadric = abstractSurface(matrix{{0,1},{1,0}}, {1,1}, {-2,-2}, 1)
abstractCubic = abstractSurface(
    -- generators are L, -E1, ..., -E6
    diagonalMatrix{1, -1, -1, -1, -1, -1, -1},
    {3,1,1,1,1,1,1}, 
    -{3,1,1,1,1,1,1},
    1)
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
abstractHypersurface ZZ := d -> (
    return new AbstractSurface from {
    	symbol IntersectionPairing => "Hypersurface of degree " | toString(d),
	symbol Hyperplane => {1},    --This means O(1)
	symbol CanonicalClass => {-4+d},    --This means O(-4+d)
	symbol Chi => 1+binomial(d-1,3)
    };
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
net AbstractSurface := X -> net X.IntersectionPairing
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
    if class X.IntersectionPairing =!= Matrix then error "IntersectionPairing not given";
    (matrix{C.DivisorClass} * X.IntersectionPairing * transpose matrix{D.DivisorClass})_(0,0)
    )
AbstractDivisor == AbstractDivisor := (C,D) -> (
    C.AbstractSurface === D.AbstractSurface and C.DivisorClass == D.DivisorClass
    )

degree AbstractDivisor := C -> (
    X := C.AbstractSurface;
    if select("Hypersurface",toString X.IntersectionPairing) =!= {} then (
    	return (first C.DivisorClass)*(4+first X.CanonicalClass);	
    );
    (matrix{C.DivisorClass} * X.IntersectionPairing * transpose matrix{X.Hyperplane})_(0,0)
    )
degree RealizedDivisor := C -> degree ideal C
genus AbstractDivisor := C -> (
    X := C.AbstractSurface;
    if select("Hypersurface",toString X.IntersectionPairing) =!= {} then (
	d := first C.DivisorClass;
	e := 4 + first X.CanonicalClass;
    	return 1/2*d*e*(d+e-4)+1;	
    );
    K := abstractDivisor(X.CanonicalClass,X);
    1/2*((K+C)*C)+1
    )
genus RealizedDivisor := C -> genus ideal C
chi AbstractDivisor := C -> (
    X := C.AbstractSurface;
    K := abstractDivisor(X.CanonicalClass,X);
    1/2 * (C * (C-K)) + X.Chi
    )

--Smoothness and irreducibility--

isSmooth = method()
isSmooth Ideal := (I) -> (
    c := codim I;
    dim(I + minors(c, jacobian I)) == 0
    )
isSmooth RealizedSurface := X -> isSmooth ideal X
isSmooth RealizedDivisor := C -> isSmooth ideal C

irreducibleOnCubic = method()
irreducibleOnCubic AbstractDivisor := Boolean => (C) -> (
    --Checks whether a divisor class on the abstract cubic is irreducible
    X := C.AbstractSurface;
    if X =!= abstractCubic then error "expected a divisor class on the cubic surface";
    H := abstractDivisor(X.Hyperplane,X);
    twentysevenLines := linesOnCubic();
    any(twentysevenLines, L -> L.DivisorClass == C.DivisorClass)
    or -- these are the conics:
    any(twentysevenLines, L -> (H-L).DivisorClass == C.DivisorClass)
    or (
     all(twentysevenLines, L -> L * C >= 0)
      and
     C*C > 0
     )
    )

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
    kk := coefficientRing R;
    -- create the polynomial ring.
    if X === abstractCubic then (
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
            symbol ExtraData => (phi, points)
            }
        );
    if X === abstractQuadric then (
        IQ := ideal(R_0*R_3-R_1*R_2);
        return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => IQ,
	    symbol ExtraData => (ideal(R_0,R_1),ideal(R_0,R_2))
	    }
        );
    if select("Hypersurface",X.IntersectionPairing) =!= {} then (        
	return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => ideal random(4+first X.CanonicalClass,R),
	    symbol ExtraData => null
	    }    	
    );
    error "Not implemented yet";
    )
realize (AbstractDivisor,RealizedSurface) := opts -> (C, X) -> (
    if C.AbstractSurface =!= X.AbstractSurface then error "expected divisor class on the given surface";
    if X.AbstractSurface === abstractCubic then (
        -- check irreducibility from numerical criterion
        (phi,pts) := X.ExtraData;
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
    if X.AbstractSurface === abstractQuadric then (
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
    if select("Hypersurface",toString X.AbstractSurface.IntersectionPairing) =!= {} then (
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
realize AbstractDivisor := opts -> C -> (
    X := realize C.AbstractSurface;
    realize(C,X)
    )


--Rao Module--


minimalCurveInLiaisonClass=method()
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
    --todo sort degList
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
    Ldg := apply(L, C -> (degree C, genus C));
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

effectiveDivisors = method()
effectiveDivisors (RealizedSurface,List) := (X,Data) -> (
    --List all RealizedDivisors of the RealizedSurface X satisfying Data
    if X.AbstractSurface === abstractCubic then (
	--Data = {degree of plane model,space degree}
	assert(#Data == 2);
	a := Data#0;
    	d := Data#1;
    	dlist := apply(select(partitions(3*a-d),p->#p<=6),q-> {a} | toList q | splice{(6-#q):0});    
    	Lad := apply(dlist,L -> abstractDivisor(L,abstractCubic));
    	Lad = select(Lad, ad-> irreducibleOnCubic ad);
    	return apply(Lad, ad -> realize(ad,X));
    );
    if X.AbstractSurface === abstractQuadric then (
	--Data = {degree}: creates all diviors (a,b) where a+b = degree
	assert(#Data == 1);
	maxdeg := ceiling(1/2*first Data);
	return for a from 1 to maxdeg list (
       	    C := abstractDivisor({a,first Data - a},abstractQuadric);
	    realize(C,X)
	)
    );
    if select("Hypersurface",toString X.AbstractSurface.IntersectionPairing) =!= {} then (
    	--Data = {maxdeg}: creates divisors of degree 1..maxdeg
	return apply(first Data, d -> realize(abstractDivisor({d+1},X.AbstractSurface),X));
    );
    error "not implemented yet for your type of surface"	
)

beginDocumentation()

TEST ///
  X = abstractQuadric
  R = QQ[a,b]
  C = abstractDivisor({a,b},X)
  assert(degree C == a+b)
  assert(genus C == (a-1)*(b-1))
  assert(chi C == (a+1)*(b+1))
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
  irreducibleOnCubic C
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
  irreducibleOnCubic C
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
    X = realize(abstractHypersurface(4), Ring => S)
    C = abstractDivisor({3},X.AbstractSurface)
    degree C
    genus C
    rC = realize(C,X)
    degree rC
    genus rC
    Ld = effectiveDivisors(X,{5});
    dgTable Ld
///

TEST ///
  S = ZZ/32003[x_0..x_3];
  X = realize(abstractCubic, Ring => S);
  a = 6;
  d = 9;
  Ld = effectiveDivisors(X,{a,d});   
  dgTable Ld
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
  I=hilbertBurchComputation(M,S^3)
  I=hilbertBurchComputation(M,S^2)
  I==null
///

TEST ///
  S = ZZ/32003[x_0..x_3]
  M=coker (koszul(2,vars S)|random(S^{4:-1},S^{4:-3}));
  betti M
  dim M == 0
  time I=minimalCurveInLiaisonClass M; -- used 0.58667 seconds
  L
  assert( (degree I, genus I) == (43, 168) )
  betti res I
  omega=Ext^2(S^1/I,S^{-4});
  fomega=res omega
  betti fomega
  HRao= coker(Hom(fomega.dd_2_{0..(rank fomega_2-2)},S^{-4}))
  reduceHilbert hilbertSeries HRao
  reduceHilbert hilbertSeries M
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
needsPackage "SpaceCurves"
check "SpaceCurves"
S = ZZ/32003[x_0..x_3]
X = realize(abstractCubic, Ring => S)
a = 6
time Lrd = flatten apply({10,11,12}, d -> 
    effectiveDivisors(X,{a,d}));  -- used 3.90876 seconds
dgTable Lrd



restart
needsPackage "SpaceCurves"
S = ZZ/32003[x_0..x_3]	
Y = realize(abstractQuadric, Ring => S)
time Lrd = flatten apply(6, d -> effectiveDivisors(Y,{d+1}));
dgTable Lrd

