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
    "effectiveDivisorsOnSurface",
    "effectiveDivisorsOnCubic",
    "completeIntersectionCurves",
    "effectiveDivisors"
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
	 matrix{{0}},
	 {1},	 --Hyperplane class O(1) is denoted by 1
	 {-4+d}, --CanonicalClass is O(-d+4)
	 1+binomial(d-1,3)
	}
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
    if X.Name == "Hypersurface" then (
    	return (first C.DivisorClass)*(4+first X.CanonicalClass);	
    );
    return (matrix{C.DivisorClass} * X.IntersectionPairing * transpose matrix{X.Hyperplane})_(0,0);
    )
genus AbstractDivisor := C -> (
    X := C.AbstractSurface;
    if X.Name == "Hypersurface"  then (
	d := first C.DivisorClass;
	e := 4 + first X.CanonicalClass;
    	return 1/2*d*e*(d+e-4)+1;	
    );
    K := abstractDivisor(X.CanonicalClass,X);
    return 1/2*((K+C)*C)+1;
    )
chi AbstractDivisor := C -> (
    X := C.AbstractSurface;
    if X.Name == "Hypersurface" then (
    	return (1 - genus C);	
    );
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
            symbol ExtraData => (phi, points)
            }
        );
    if X.Name == "Quadric surface" then (
        IQ := ideal(R_0*R_3-R_1*R_2);
        return new RealizedSurface from {
	    symbol AbstractSurface => X,
	    symbol Ideal => IQ,
	    symbol ExtraData => (ideal(R_0,R_1),ideal(R_0,R_2))
	    }
        );
    if X.Name == "Hypersurface" then (        
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
    if X.AbstractSurface.Name == "Cubic surface" then (
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
realize AbstractDivisor := opts -> C -> realize(C,realize(C.AbstractSurface,Options=>opts))


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

effectiveDivisorsOnCubic = method()
effectiveDivisorsOnCubic (AbstractSurface,ZZ,ZZ) := (X,a,d) -> (
    if X.Name == "Cubic surface" then (
    	dlist := apply(select(partitions(3*a-d),p->#p<=6),q -> 
	    {a} | toList q | splice{(6-#q):0});    
    	Lad := apply(dlist,L -> abstractDivisor(L,X));
    	return select(Lad, ad-> irreducibleOnCubic ad);
    );    
    error "Not a cubic surface";
)

effectiveDivisorsOnSurface = method()
effectiveDivisorsOnSurface (AbstractSurface,ZZ) := (X,d) -> (
    --List all divisors of degree d on X
    if X.Name == "Cubic surface" then (
    	return flatten apply(toList(floor(d/3)..2*d), a -> effectiveDivisorsOnCubic(X,a,d)); 	
    );
    if X.Name == "Quadric surface" then (
	--Data = {degree}: creates all diviors (a,b) where a+b = degree
	maxdeg := ceiling(1/2*d);
	return for a from 1 to maxdeg list abstractDivisor({a,d - a},X);
    );
    if X.Name == "Hypersurface" then (
	surfd := 4 + first X.CanonicalClass;
	if d % surfd =!= 0 then return {};
	return abstractDivisor({d // surfd},X);
    );
    error "not implemented yet for your type of surface"	
)

completeIntersectionCurves  = method()
completeIntersectionCurves ZZ := d -> (
    --produce all ci curves of degree d
    div := for i from 1 to floor sqrt d when d % i == 0 list i;
    return apply(div, deg -> 
	abstractDivisor({d // deg},abstractHypersurface(deg)));            
)

effectiveDivisors = method()
effectiveDivisors ZZ := d -> (
    effectiveDivisorsOnSurface(abstractCubic,d) |
    effectiveDivisorsOnSurface(abstractQuadric,d) |
    completeIntersectionCurves(d)    
)


beginDocumentation()

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


end--------


--Generate curves on cubic surface
restart
needsPackage "SpaceCurves"
check "SpaceCurves"
S = ZZ/32003[x_0..x_3]
X = realize(abstractCubic, Ring => S)
a = 6
time Lrd = flatten apply({10,11,12}, d -> 
    effectiveDivisors(X,{a,d}));  -- used 3.90876 seconds
dgTable Lrd

--Generate curves on quadric surface
restart
needsPackage "SpaceCurves"
S = ZZ/32003[x_0..x_3]	
Y = realize(abstractQuadric, Ring => S)
time Lrd = flatten apply(6, d -> effectiveDivisors(Y,{d+1}));
dgTable Lrd

--Generate complete intersection curves
