
newPackage(
  "MultiHilbertPolynomial",
  AuxiliaryFiles => false,
  Version => "0.1",
  Date => "19 July 2017",
  Authors => {{
      Name => "Chris Eur", 
      Email => "chrisweur@gmail.com", 
      HomePage => "https://math.berkeley.edu/~ceur"}},
  Headline => "computes multigraded Hilbert polynomial",
  PackageExports => {
      "Schubert2",
      "NormalToricVarieties"
  },
  PackageImports => {
      "Schubert2",
      "NormalToricVarieties"
  },
  DebuggingMode => true,
  Reload => true
)

export {
}


hilbertPolynomial NormalToricVariety := RingElement => opts -> (
    (cacheValue (symbol hilbertPolynomial => opts))(X -> (
    if not isSmooth X
    then error "not yet implemented for singular toric varieties";
    if not isComplete X
    then error "not yet implemented for noncomplete toric varieties";
    i := local i;
    n := # rays X;
    r := rank picardGroup X;
    pt := base apply(0..r-1, j -> i_j);
    V := abstractVariety(X,pt);
    S := intersectionRing V;
    R := coefficientRing S;
    sigma := (max X)#0;
    sigmaVee := select(n, i -> not member(i, sigma));
    f := ((matrix{(gens S)_sigmaVee} * ((fromCDivToPic X)_sigmaVee)^(-1) * transpose vars R))_(0,0);
    chi OO_V(f)
)))


{*
-- to compute the Hilbert polynomial, we simply interpolated the coefficients
-- for a sufficiently large number of points in the nef cone.  Is there a
-- better way?
hilbertPolynomial( NormalToricVariety,ZZ) := RingElement => opts -> (X,k) -> (
    if not isSmooth X  
    then error "not (yet?) implemented for singular toric varieties";    
    d := dim X;
    r := rank picardGroup X; -- update pic to picardGroup
    R := (ZZ/2)(monoid [local T_0.. local T_r]);
    monomialExp := rsort apply(flatten entries basis({d},R), 
      r -> drop(first exponents r,-1));
    m := #monomialExp;
    nefX := transpose nefGenerators X; -- update nef to nefGenerators, transpose??
    ell := rank source nefX;
    b := ceiling min(binomial(d+r,r), log_ell binomial(d+r,r));
    while true do (
      Sigma := (toList ((set(0..b-1)) ^** ell));
      nefPoints := unique rsort apply(Sigma,
      	s -> first entries transpose (nefX * transpose matrix {toList s}));
      if #nefPoints >= m then (
	A := matrix table(nefPoints, monomialExp, 
      	  (p,e) -> product(r, j -> (1/1) * (p#j) ^ (e#j)));
	if det( transpose(A) * A ) != 0 then break);
      b = b+1);
    A = (transpose(A)*A)^(-1)* transpose(A);  -- pseudoinverse
    B := transpose matrix {apply(nefPoints, p -> hilbertFunction(p, ring X))};
    hilbertCoeffs := first entries transpose (A * B);
    i := symbol i;
    S := QQ(monoid [i_0..i_(r-1)]);
    sum(m, j -> hilbertCoeffs#j*product(r, k -> S_k^(monomialExp#j#k)))
)
*}

hilbertPolynomial (NormalToricVariety,Module) := RingElement => opts -> 
(X,M) -> (
  if not isHomogeneous M then error "expected a homogeneous module";
  if ring X =!= ring M then error "expected module over the Cox ring";
  h := hilbertPolynomial X;
  R := ring h;
  r := numgens R;
  f := poincare M;
  p := pairs standardForm f;
  if #p === 0 then 0_R
  else sum(p, (d,c) -> (
      shift := apply(r, j -> if d#?j then R_j - d#j else R_j);
      c * substitute(h,matrix{shift})))
)


hilbertPolynomial (NormalToricVariety, Ring) := RingElement => opts ->
(X,S) -> hilbertPolynomial(X, S^1, opts)
hilbertPolynomial (NormalToricVariety, Ideal) := RingElement => opts ->
(X,I) -> hilbertPolynomial(X, (ring I)^1/I, opts)
hilbertPolynomial (NormalToricVariety, CoherentSheaf) := RingElement => 
opts -> (X,F) -> hilbertPolynomial(X, F.module, opts)

{*
hilbertPolynomial (NormalToricVariety,MultigradedBettiTally) := RingElement =>
opts -> (X,B) -> (
  h := hilbertPolynomial X;
  R := ring h;
  r := numgens R;
  f := poincare(X,B);
  p := pairs standardForm f;
  if #p === 0 then 0_R
  else sum(p, (d,c) -> (
      shift := apply(r, j -> if d#?j then R_j - d#j else R_j);
      c * substitute(h,matrix{shift}))))
*}


abstractVariety(NormalToricVariety,AbstractVariety) := opts -> (Y,B) -> (
    if not isSimplicial Y then error "abstract variety for non-simplicial toric varieties not yet implemented";
    if not Y.cache#?(abstractVariety, B) then Y.cache#(abstractVariety,B) = (
	kk := intersectionRing B;
	IY := intersectionRing Y;
	amb := kk[gens ambient IY, Join=>false];
	IY = amb/(sub(ideal IY, vars amb));
	aY := abstractVariety(dim Y, IY);
	aY.TangentBundle = abstractSheaf(aY, Rank=>dim Y, ChernClass => product(gens IY, x -> 1+x));
	-- Now we determine the mapping 'integral':
	raysY := transpose matrix rays Y;
	onecone := first max Y;
	pt := (abs det raysY_onecone) * product(onecone, i -> IY_i);
	if size pt != 1 then error "cannot define integral: some strange error has occurred";
	mon := leadMonomial pt;
	cf := leadCoefficient pt;
	if not liftable(cf, QQ) then error "cannot create integral function";
	a := 1 / lift(cf, QQ);
	integral IY := (f) -> a * coefficient(mon, f);
	-- a check:
	--print for f in max Y list product(f, i -> IY_i);
	assert all(max Y, f -> integral(product(f, i -> IY_i)) == 1/(abs(det raysY_f)));
	aY
	);
    Y.cache#(abstractVariety, B)
)

intersectionRing NormalToricVariety := (X) -> (
    if not isSimplicial X then error "intersection ring for non-simplicial toric varieties not yet implemented";
    if isSimplicial X then (
	S := ring X;
	n := numgens S;
	t := getSymbol "t";
	R := QQ(monoid [t_0 .. t_(n-1)]);
	phi := map(R,S,gens R);
	M := phi dual monomialIdeal X;
	L := ideal(vars R * (matrix rays X) ** R);
	R/(M+L)
	)
    )

beginDocumentation()

doc ///
    Key
        (hilbertPolynomial, NormalToricVariety)
    Headline 
        computes the Hilbert polynomial
    Usage 
        hilbertPolynomial X
    Inputs 
        X:NormalToricVariety
	    a smooth projective toric variety
    Outputs 
        :RingElement 
	    the Hilbert polynomial of X
    Description
        Text
            The Hilbert polynomial of a smooth projective toric
    	    variety $X$ is the Euler characteristic of
    	    $OO_X(i_0,...,i_r)$ where $r$ is the rank of the Picard
    	    group of X and i_0,...,i_r are formal variables.  The
    	    Hilbert polynomial agrees with the Hilbert function when
    	    evaluated at any point in the nef cone.
    	Text
            This example illustrates the projective plane.
    	Example  
    	   PP2 = projectiveSpace 2;
	   h = hilbertPolynomial PP2
	   R = ring h;
	   all(5, i -> sub(h,R_0 => i) == hilbertFunction(i,ring PP2))
	   hilbertPolynomial(ring PP2, Projective => false)
	Text
	    This example illustrates the product of two projective 3-spaces.
	Example
           P3P3 = (projectiveSpace 3) ^** 2;
	   factor hilbertPolynomial P3P3
	Text
	    This example illustrates the Hirzebruch surface 5.
    	Example
	   H5 = hirzebruchSurface 5;
	   factor hilbertPolynomial H5
    SeeAlso
        "Making normal toric varieties"
        (isSmooth, NormalToricVariety)
        (isProjective, NormalToricVariety)
///   


doc ///
    Key
        (hilbertPolynomial, NormalToricVariety, Module)
	(hilbertPolynomial, NormalToricVariety, CoherentSheaf)
	(hilbertPolynomial, NormalToricVariety, Ideal)
    Headline 
        computes the Hilbert polynomial of a module or coherent sheaf
    Usage 
        hilbertPolynomial(X,M)
	hilbertPolynomial(X,F)
	hilbertPolynomial(X,I)
    Inputs 
        X:NormalToricVariety
	    a smooth projective toric variety
	M:Module
	    a graded module over the Cox ring of X
	F:CoherentSheaf
	    a coherent sheaf over X
	I:Ideal
	    a graded ideal in the Cox ring of X
    Outputs 
        :RingElement 
	    the Hilbert polynomial
    Description
        Text
            The Hilbert polynomial of a coherent sheaf $F$ over a
	    smooth projective toric variety $X$ is the Euler characteristic
    	    of $F(i_0,...,i_r)$ where $r$ is the rank of the Picard
    	    group of X and i_0,...,i_r are formal variables.  The
    	    Hilbert polynomial agrees with the Hilbert function when
    	    evaluated at any point sufficiently far in the interior
	    of the nef cone.
	Text
	    For an ideal $I$ in the Cox ring $S$, this computes the Hilbert
	    polynomial of the coherent sheaf associated to $S/I$.
    	Text
            This example illustrates the ideal over the product of two
	    projective lines.
    	Example  
    	  P1P1 = hirzebruchSurface 0;
	  S = ring P1P1;
	  R = ring hilbertPolynomial P1P1;
	  I = ideal(S_0^2*S_3^2 - S_0*S_2*S_1^2);
	  hilbertPolynomial(P1P1, I)
	  hilbertPolynomial(P1P1, S^1/I)
	  h = hilbertPolynomial(P1P1, module I)
	  R = ring h;
	  any({1,1}..{3,3}, j -> sub(h, {R_0 => j_0, R_1 => j_1}) == hilbertFunction(j,module I))
	Text
	    This example illustrates the cotangent bundle of Hirzebruch
	    surface.
	Example
           H3 = hirzebruchSurface 3;
	   R = ring hilbertPolynomial H3;
	   h = hilbertPolynomial(H3, cotangentSheaf H3)
	Text
	    This example illustrates the Hirzebruch surface 5.
    	Example
	   H5 = hirzebruchSurface 5;
	   factor hilbertPolynomial H5
    SeeAlso
        "Making normal toric varieties"
        (isSmooth, NormalToricVariety)
        (isProjective, NormalToricVariety)
///


TEST /// 
--Test 0: multigraded Hilbert polynomial for structure sheaves of toric varieties
P2 = projectiveSpace 2;
h = hilbertPolynomial P2;
R = ring h;
assert(h === (1/2)*(R_0+2)*(R_0+1));

P2P2 = (projectiveSpace 2) ^** 2;
h = hilbertPolynomial P2P2;
R = ring h;
assert(h ===  (1/2)*(R_0+2)*(R_0+1)* (1/2)*(R_1+2)*(R_1+1))

H3 = hirzebruchSurface 3;
h = hilbertPolynomial H3;
R = ring h;
assert(h === (1/2)*(R_1+1)*(2*R_0+3*R_1+2));
///

TEST ///
-- Test 1: multigraded Hilbert polynomial for coherent sheaves
P1P1 = hirzebruchSurface 0;
S = ring P1P1;
R = ring hilbertPolynomial P1P1;
I = ideal(S_0^2*S_3^2 - S_0*S_2*S_1^2);
assert(hilbertPolynomial(P1P1, module I) === (R_0-1)*(R_1-1));
assert(hilbertPolynomial(P1P1, S^1/I) === 2*R_0 + 2*R_1);
assert(hilbertPolynomial(P1P1,S^0) === 0_R);

H3 = hirzebruchSurface 3;
R = ring hilbertPolynomial H3;
assert(hilbertPolynomial(H3, cotangentSheaf H3) === -(R_1+1)*(2*R_0+3*R_1+2)+(R_1+1)*(2*R_0+3*R_1)+(1/2)*(R_1)*(2*R_0+3*R_1+5)+(1/2)*(R_1)*(2*R_0+3*R_1-1));

{* Are we actually computing the Chern character of f_!OO_X?
X2 = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{0,-1,2},{0,0,-1},{-1,1,-1},{-1,0,-1},{-1,-1,0}},{{0,1,2},{0,2,3},{0,3,4},{0,4,5},{0,1,5},{1,2,7},{2,3,7},{3,4,7},{4,5,6},{4,6,7},{5,6,7},{1,5,7}});
hilbertPolynomial X2
nefGenerators X2
*}
///


end

uninstallPackage "MultiHilbertPolynomial"
restart
installPackage "MultiHilbertPolynomial"
check MultiHilbertPolynomial
Z = hirzebruchSurface 0
P2 = projectiveSpace 2
hilbertPolynomial P2
VS = P2 ^** 2
hilbertPolynomial VS
Z = Z^**2
time hilbertPolynomial Z
R = ring Z
I = ideal(x_0^2*x_3^2 - x_0*x_2*x_1^2)
hilbertPolynomial(Z, module I)
hilbertPolynomial(Z, R^1/I)
X^**2
R = QQ[x,y,z];
I = ideal"x2,y3";
multigradedHilbertPolynomial(I)

