
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
    "isFibration"    
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

map(NormalToricVariety, NormalToricVariety, Matrix) := ToricMap => opts -> (Y,
  X,A) -> (
  if ring A =!= ZZ then error "expected an integer matrix";
  if rank source A != dim X then error ("expected source to be the lattice " |
    "of one-parameter subgroups in " | toString X);
  if rank target A != dim Y then error ("expected target to be the lattice " |
    "of one-parameter subgroups in " | toString Y);  
  return new ToricMap from {
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

-- local method; produces the outer normal vectors for each max cone
outerNormals = method()
outerNormals (NormalToricVariety,List) := Matrix => (X,sigma) -> (
  if not X.cache.?outerNormals then (
    X.cache.outerNormals = new MutableHashTable);
  if not X.cache.outerNormals#?sigma then (
    V := transpose matrix rays X;
    X.cache.outerNormals#sigma = transpose (fourierMotzkin V_sigma)#0);
  return X.cache.outerNormals#sigma)

isWellDefined ToricMap := Boolean => f -> (
  X := source f;
  Y := target f;
  V := transpose matrix rays X;
  A := matrix f;
  return all(max X, sigma -> any(max Y, 
      tau -> all(flatten entries ( outerNormals(Y, tau) * A * V_sigma), 
	i -> i <= 0))))

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

uninstallPackage "ToricMorphisms"
restart
installPackage "ToricMorphisms"
H2 = hirzebruchSurface 2
PP1 = projectiveSpace 1
f = map(PP1,H2,matrix{{1,0}})
isWellDefined f
isSurjective f
isFibration f



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

