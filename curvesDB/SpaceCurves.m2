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
    "AbstractSurface",
    "DivisorClass",
    "divisorClass",
    "abstractSurface",
    "abstractQuadric",
    "abstractCubic",
    "realizeSurface",
    "CanonicalClass",
    "Hyperplane",
    "IntersectionPairing",
    "Class",     --Different name??   
    "Chi" -- Euler characteristic of OO_X.
    }

AbstractSurface = new Type of HashTable
DivisorClass = new Type of HashTable

abstractSurface = method()
abstractSurface(Matrix, List, List, ZZ) := (M, hyperplane, canonical, surfaceChi) -> (
    -- M is a square matrix over the integers, which is the
    -- intersection pairing of Num(X), for some surface X.
    rho := numRows M;
    if rho != numColumns M then error "expected square matrix";
    -- TODO: add hodge index.
    new AbstractSurface from {
        IntersectionPairing => M,
        Hyperplane => hyperplane,
        CanonicalClass => canonical,
        Chi => surfaceChi
        }
    )

abstractQuadric = abstractSurface(matrix{{0,1},{1,0}}, {1,1}, {-2,-2}, 1)
abstractCubic = abstractSurface(
    -- generators are L, -E1, ..., -E6
    diagonalMatrix{1, -1, -1, -1, -1, -1, -1},
    {3,1,1,1,1,1,1}, 
    -{3,1,1,1,1,1,1},
    1)

divisorClass = method()
divisorClass(List, AbstractSurface) := (C, X) -> (
    new DivisorClass from {
        symbol Class => C,
        symbol AbstractSurface => X
        }
    )

ZZ * DivisorClass := (n,D) -> (
    divisorClass(n * D.Class, D.AbstractSurface)
    )
DivisorClass + DivisorClass := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    divisorClass(C.Class + D.Class, D.AbstractSurface)
    )
DivisorClass - DivisorClass := (C,D) -> (
    assert(C.AbstractSurface === D.AbstractSurface);
    divisorClass(C.Class - D.Class, D.AbstractSurface)
    )

DivisorClass * DivisorClass := (C,D) -> (
    X := C.AbstractSurface;
    assert(X === D.AbstractSurface);
    (matrix{C.Class} * X.IntersectionPairing * transpose matrix{D.Class})_(0,0)
    )

degree(DivisorClass) := C -> (
    X := C.AbstractSurface;
    (matrix{C.Class} * X.IntersectionPairing * transpose matrix{X.Hyperplane})_(0,0)
    )
genus(DivisorClass) := C -> (
    X := C.AbstractSurface;
    K := divisorClass(X.CanonicalClass,X);
    1/2*((K+C)*C)+1
    )
chi DivisorClass := C -> (
    X := C.AbstractSurface;
    K := divisorClass(X.CanonicalClass,X);
    1/2 * (C * (C-K)) + X.Chi
    )

existsCurveOnCubic = method()
existsCurveOnCubic DivisorClass := Boolean => (C) -> (
    -- todo
    )

existsCurveOnQuadric = method()
existsCurveOnQuadric DivisorClass := Boolean => (C) -> (
    -- todo
    )

smoothCurveOnSurface = method(Options => {Ring => null, CoefficientRing => ZZ/32003})
smoothCurveOnSurface DivisorClass := opts -> (C) -> (
    -- create a curve, if possible
    )

realizeSurface = method(Options => options smoothCurveOnSurface)
realizeSurface AbstractSurface := opts -> X -> (
    -- Note: this is in P^3
    R := if opts#Ring =!= null then 
        opts#Ring 
      else (
        x := getSymbol "x";
        opts.CoefficientRing[x_0..x_3]
      );
    -- create the polynomial ring.
    if X === abstractCubic then (
        return null;
        );
    if X === abstractQuadric then (
        IQ := ideal(R_0*R_3-R_1*R_2);
        return (IQ, ideal(R_0, R_1), ideal(R_0, R_2))
        );
    error "don't know how to realize your pathetic surface";
    )
    
beginDocumentation()

TEST ///
  X = abstractQuadric
  R = QQ[a,b]
  C = divisorClass({a,b},X)
  assert(degree C == a+b)
  assert(genus C == (a-1)*(b-1))
  assert(chi C == (a+1)*(b+1))
///

TEST ///
  X = abstractCubic
  R = QQ[a,b_1..b_6]
  C = divisorClass(gens R,X)
  degree C
  genus C
  factor chi C
///

end--

restart
needsPackage "SpaceCurves"
check "SpaceCurves"

IQ = realizeSurface(abstractQuadric, Ring => QQ[a..d])

doc ///
Key
  SpaceCurves
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

