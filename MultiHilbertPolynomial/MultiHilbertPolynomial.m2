
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
      "NormalToricVarieties",
      "Schubert2"
  },
  PackageImports => {
      "NormalToricVarieties",
      "Schubert2"
  },
  DebuggingMode => true,
  Reload => true
)

export {
}


hilbertPolynomial NormalToricVariety := RingElement => opts -> X -> (
    i := local i;
    n := # rays X;
    r := rank picardGroup X;
    pt := base apply(0..r-1, j -> i_j);
    V := abstractVariety(X,pt);
    S := intersectionRing V;
    R := coefficientRing S;
    sigma := (max X)#0;
    sigmaVee := select(n, i -> not member(i, sigma));
    chi OO ((matrix{(gens S)_sigmaVee} * ((fromCDivToPic X)_sigmaVee)^(-1) * transpose vars R))_(0,0)
)


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

end

restart
needsPackage "MultiHilbertPolynomial"
Z = hirzebruchSurface 0
Z = Z^**2
time hilbertPolynomial Z
R = ring Z
I = ideal(x_0^2*x_3^2 - x_0*x_2*x_1^2)
hilbertPolynomial(Z, module I)
X^**2
R = QQ[x,y,z];
I = ideal"x2,y3";
multigradedHilbertPolynomial(I)

