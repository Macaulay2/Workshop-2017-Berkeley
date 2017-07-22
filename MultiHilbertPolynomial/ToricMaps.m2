
newPackage(
  "ToricMaps",
  AuxiliaryFiles => false,
  Version => "0.1",
  Date => "19 July 2017",
  Authors => {
      {
      Name => "Chris Eur", 
      Email => "chrisweur@gmail.com", 
      HomePage => "https://math.berkeley.edu/~ceur"},
      {
      Name => "Justin Chen", 
      Email => "jchen@math.berkeley.edu", 
      HomePage => "https://math.berkeley.edu/~jchen"},
      {
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}
      },
  Headline => "routines for working with toric morphisms",
  PackageExports => {
      "NormalToricVarieties"
  },
  PackageImports => {
      "NormalToricVarieties",
      "FourierMotzkin"
  },
  DebuggingMode => true,
  Reload => true
)

export {
    "ToricMap",
    "isFibration",
    "outerNormals",
    "isProper"    
}


------------------------------------------------------------------------------
-- toric morphisms


ToricMap = new Type of HashTable
ToricMap.synonym = "toric map"
source ToricMap := NormalToricVariety => f -> f.source
target ToricMap := NormalToricVariety => f -> f.target
matrix ToricMap := Matrix => opts -> f -> f.matrix

net ToricMap := f -> net matrix f
ToricMap#{Standard,AfterPrint} = ToricMap#{Standard,AfterNoPrint} = f -> (
  << endl;				  -- double space
  << concatenate(interpreterDepth:"o") << lineNumber << " : ToricMap ";
  << net target f << " <--- " << net source f << endl;)

map(NormalToricVariety, NormalToricVariety, Matrix) := ToricMap => opts -> (Y,
  X,A) -> (
  if ring A =!= ZZ then error "expected an integer matrix";
  if rank source A != dim X then error ("expected source to be the lattice " |
    "of one-parameter subgroups in " | toString X);
  if rank target A != dim Y then error ("expected target to be the lattice " |
    "of one-parameter subgroups in " | toString Y);  
  new ToricMap from {
    symbol source => X,
    symbol target => Y,
    symbol matrix => A,
    symbol cache => new CacheTable})

map(NormalToricVariety, NormalToricVariety, ZZ) := ToricMap => opts -> (Y,
  X,i) -> (
  m := dim Y;
  n := dim X;
  if i === 0 then return map(Y,X, map(ZZ^m, ZZ^n, 0))
  else if m === n then return map(Y,X,map(ZZ^m, ZZ^n, i))
  else error "expect 0, or source and target to have same dimension")

NormalToricVariety#id = X -> map(X,X,1)

- ToricMap := ToricMap => f -> new ToricMap from {
  symbol source => source f,
  symbol target => target f,
  symbol matrix => - matrix f,
  symbol cache => new CacheTable}

ZZ * ToricMap := ToricMap => (r,f) -> new ToricMap from {
  symbol source => source f,
  symbol target => target f,
  symbol matrix => r * matrix f,
  symbol cache => new CacheTable}

ToricMap * ToricMap := ToricMap => (g,f) -> (
  if target f =!= source g then error "expected composable maps";
  new ToricMap from {
    symbol source => source f,
    symbol target => target g,
    symbol matrix => (matrix g) * (matrix f),
    symbol cache => new CacheTable})

-- local method; produces the outer normal vectors for each max cone
-- at the moment exported for dubugging purposes
outerNormals = method()
outerNormals (NormalToricVariety,List) := Matrix => (X,sigma) -> (
  if not X.cache.?outerNormals then (
    X.cache.outerNormals = new MutableHashTable);
  if not X.cache.outerNormals#?sigma then (
    V := transpose matrix rays X;
    X.cache.outerNormals#sigma = transpose (fourierMotzkin V_sigma)#0);
  return X.cache.outerNormals#sigma)

isWellDefined ToricMap := Boolean => f -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys f;
    expectedKeys := set{ symbol source, symbol target, symbol matrix, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then 
	        << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then 
	        << "-- missing keys(s): " << toString missing << endl);
    	return false);
    --Check types
    if not instance(f.source, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `source' to be a NormalToricVariety" << endl);
	return false);
    if not instance(f.target, NormalToricVariety) then (
	if debugLevel > 0 then (
	    << "-- expected `target' to be a NormalToricVariety" << endl);
	return false);
    if not instance(f.matrix, Matrix) then (
	if debugLevel > 0 then (
	    << "-- expected `matrix' to be a Matrix" << endl);
	return false);
    if ring matrix f =!= ZZ then (
    	if debugLevel > 0 then (
	    << "-- expected `matrix' over the integers" << endl);
	return false);	 
    if not instance(f.cache, CacheTable) then (
    	if debugLevel > 0 then (
	    << "-- expected `f.cache' to be a CacheTable" << endl);
    	return false);
    --Check mathematical structure
    X := source f;
    Y := target f;
    A := matrix f;
    if rank source A =!= dim X then (
    	if debugLevel > 0 then (
	    << "-- expected number of columns of the matrix to equal the dimension of the source variety");
	return false);
    if rank target A =!= dim Y then (
    	if debugLevel > 0 then (
	    << "-- expected number of rows of the matrix to equal the dimension of the target variety");
	return false);
    V := transpose matrix rays X;
    if not all(max X, sigma -> any(max Y, 
      	tau -> all(flatten entries ( outerNormals(Y, tau) * A * V_sigma), 
	i -> i <= 0))) then (
    	if debugLevel > 0 then (
	    << "-- expected image of each maximal cone to be contained in some maximal cone");
	return false);
    true
)


isProper = method()
isProper ToricMap := Boolean => f -> (
    X := source f;
    Y := target f;
    if isComplete X then return true;
    if (isComplete Y and not isComplete X) then return false;
    A := matrix f;
    rayMatrixX := transpose matrix rays X;
    rayMatrixY := transpose matrix rays Y;
    coneTable := new MutableHashTable;
    for sigma in max X do (
	for tau in max Y do ( 
      	if all(flatten entries (outerNormals(Y, tau) * A * rayMatrixX_sigma), i -> i <= 0) then (
	    if not coneTable#?tau then coneTable#tau = {sigma}
	    else coneTable#tau = coneTable#tau|{sigma}
	    )
	)
    );
    K := mingens ker A;
    for tau in max Y do (
    	indicesOverTau := unique flatten coneTable#tau;
	raysOverTau := entries transpose rayMatrixX_indicesOverTau;
	conesOverTau := apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)));
	varietyOverTau := normalToricVariety(raysOverTau, conesOverTau); 
	liftTau := rayMatrixY_tau//A | K | -K;
	boundaries := select(orbits(varietyOverTau,dim X - rank liftTau + 1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2);	
	for C in boundaries do (
		supportHyperplanes := first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then return false;
	);
    );
    true
)


isFibration = method()
isFibration ToricMap := Boolean => f -> 1 == minors(dim target f, matrix f)

isSurjective ToricMap := Boolean => f -> rank matrix f == dim target f





end

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
H2 = hirzebruchSurface 2
PP1 = projectiveSpace 1
f = map(PP1,H2,matrix{{1,0}})
assert isWellDefined f
assert isProper f

Y = normalToricVariety(rays H2, drop(max H2, -1))
isWellDefined Y
f = map(PP1, Y, matrix{{1,0}})
assert isWellDefined f
assert not isProper f

g = map(Y, PP1, matrix{{0},{1}})
assert isWellDefined g
assert isProper g

P1A1 = (affineSpace 1) ** (projectiveSpace 1)
A1 = affineSpace 1
h = map(A1, P1A1, matrix{{1,0}})
assert isWellDefined h
assert isProper h

X = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{-1,0,0},{0,0,-1}},{{0,1},{1,2,3},{1,3,4}})
Y = (projectiveSpace 1) ** (affineSpace 1)
f = map(Y,X,matrix{{1,0,0},{0,1,0}})
assert isWellDefined f
assert not isProper f

X = normalToricVariety({{0,-1,0},{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0},{1,4},{2,3,4},{2,3,5}})
Y = normalToricVariety({{0,-1},{1,0},{0,1},{-1,0}},{{0},{1},{2,3}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
assert isWellDefined f
assert not isProper f

X' = normalToricVariety(rays X, append(max X, {1,5}))
f = map(Y,X',A)
assert isWellDefined f
assert not isProper f

X'' = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{0,4},{1,2,3},{1,2,4}})
Y' = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y',X'',A)
assert isWellDefined f
assert isProper f



///


end

uninstallPackage "ToricMaps"
restart
installPackage "ToricMaps"


needsPackage "FourierMotzkin"
X'' = normalToricVariety({{1,0,0},{0,1,0},{-1,0,0},{0,0,1},{0,0,-1}},{{0,3},{0,4},{1,2,3},{1,2,4}})
Y' = normalToricVariety({{1,0},{0,1},{-1,0}},{{0},{1,2}})
A = matrix{{1,0,0},{0,1,0}}
f = map(Y',X'',A)
assert isWellDefined f
assert isProper f

    X = source f
    Y = target f
    if isComplete X then return true
    if (isComplete Y and not isComplete X) then return false
    A = matrix f
    rayMatrixX = transpose matrix rays X
    rayMatrixY = transpose matrix rays Y
    coneTable = new MutableHashTable
    for sigma in max X do (
	for tau in max Y do ( 
      	if all(flatten entries (outerNormals(Y, tau) * A * rayMatrixX_sigma), i -> i <= 0) then (
	    if not coneTable#?tau then coneTable#tau = {sigma}
	    else coneTable#tau = coneTable#tau|{sigma}
	    )
	)
    )
    K = mingens ker A
    tau = (max Y)_0
    	indicesOverTau = unique flatten coneTable#tau
	raysOverTau = entries transpose rayMatrixX_indicesOverTau
	conesOverTau = apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)))
	varietyOverTau = normalToricVariety(raysOverTau, conesOverTau) 
	liftTau = rayMatrixY_tau//A | K | -K
	boundaries = select(orbits(varietyOverTau,dim X - rank liftTau +1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2)
	
	for C in boundaries do (
		supportHyperplanes = first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then print "crap"
	)

 tau = (max Y)_1
    	indicesOverTau = unique flatten coneTable#tau
	raysOverTau = entries transpose rayMatrixX_indicesOverTau
	conesOverTau = apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)))
	varietyOverTau = normalToricVariety(raysOverTau, conesOverTau) 
	liftTau = rayMatrixY_tau//A | K | -K
	boundaries = select(orbits(varietyOverTau,dim X - rank liftTau +1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2)
	
	for C in boundaries do (
		supportHyperplanes = first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then print "crap"
	)










H2 = hirzebruchSurface 2
PP1 = projectiveSpace 1
f = map(PP1,H2,matrix{{1,0}})
isWellDefined f
isSurjective f
isFibration f

H2 = hirzebruchSurface 2
outerNormals(H2, {2,3})


Bl = normalToricVariety({{0,1},{1,1},{1,0}},{{0,1},{1,2}})
AA2 = normalToricVariety({{0,1},{1,0}},{{0,1}})
f = map(Bl, AA2, id_(ZZ^2))
isWellDefined f
g = map(AA2, Bl, id_(ZZ^2))
isWellDefined g

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

--Notes
--if source complete then any map is proper
--will only deal with cases when source and have convex support of full dimension


isConvFullSupp := X -> (
    V = transpose matrix rays X
    if not all(max X, sigma -> minors(dim X, V_sigma)=!=0) then (
    	if debugLevel > 0 then (
	    << "-- some cones are not full dimensional" << endl);
	return false);
    boundaries := flatten apply (max X, sigma ->
	select(subsets(#sigma-1, sigma), tau -> sigma == select(max X, sig -> isSubset(tau,sig))) 
    	)
)


restart
needsPackage "ToricMaps"
needsPackage "FourierMotzkin"

X = normalToricVariety({{1,0,0},{0,1,0},{0,0,1},{-1,0,0}},{{0,1},{1,2,3}})
Y = (projectiveSpace 1) ** (affineSpace 1)

peek X
peek Y

A = matrix{{1,0,0},{0,1,0}}
f = map(Y,X,A)
rayMatrixX := transpose matrix rays X;
rayMatrixY := transpose matrix rays Y;
K = mingens ker A
    coneTable := new MutableHashTable;
    for sigma in max X do (
	for tau in max Y do ( 
      	if all(flatten entries (outerNormals(Y, tau) * A * rayMatrixX_sigma), i -> i <= 0) then (
	    if not coneTable#?tau then coneTable#tau = {sigma}
	    else coneTable#tau = coneTable#tau|{sigma}
	    )
	)
    );
keys coneTable
values coneTable
tau = (max Y)_1
    	indicesOverTau := unique flatten coneTable#tau;
	raysOverTau := entries transpose rayMatrixX_indicesOverTau;
	conesOverTau := apply(coneTable#tau, sigma -> apply(sigma, i -> position(indicesOverTau, j -> j===i)));
	varietyOverTau := normalToricVariety(raysOverTau, conesOverTau); 
	boundaries := select(orbits(varietyOverTau,1), C ->  #select(max varietyOverTau, sig -> isSubset(C,sig))<2);
	liftTau := rayMatrixY_tau//A | K | -K;
	apply(boundaries, C -> (
		supportHyperplanes := first fourierMotzkin liftTau;
		if all(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)) > 0) then return false;
	));
C = boundaries_0  
supportHyperplanes := first fourierMotzkin liftTau;  
apply(numcols supportHyperplanes, i -> #delete(0, flatten entries ((matrix rays varietyOverTau)^C * supportHyperplanes_i)))    
    
    
M = random(ZZ^3,ZZ^5)
K = mingens ker M
B = transpose matrix {{0,4,-2}}
B//M
K | -K
