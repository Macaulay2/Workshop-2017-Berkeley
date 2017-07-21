newPackage(
	"InverseSystems",
    	Version => "1.1", 
    	Date => "July 21, 2017",
    	Authors => {{Name => "David Eisenbud", 
		  Email => "de@msri.org",
		  Name => "Matthew Mastroeni",
		  Email => "mastroe2@illinois.edu",
		  Name => "Rebecca R.G.",
		  Email => "rirebhuh@syr.edu"
		  }},
    	Headline => "Macaulay inverse systems via differentiation and divided powers",
    	DebuggingMode => false
    	)


export {"inverseSystem",
        "toDividedPowers",
        "fromDividedPowers",
	"isStandardGradedPolynomialRing",
	"contractInDegree",
	"contractKernelInDegree",
	"contractImageInDegree",
	--option names (symbols):
	"PowerBound",
	"DividedPowers",
	"toDual", 
	"fromDual"
	}


///
restart
uninstallPackage "InverseSystems"
installPackage "InverseSystems"
check "InverseSystems"
///


isStandardGradedPolynomialRing = method()
isStandardGradedPolynomialRing Ring := R ->(
    isField coefficientRing R and
       isPolynomialRing R and
       all(gens R, v->(degree v)=={1})
       )


toDividedPowers = method()
toDividedPowers RingElement := p -> (
    --the following routine takes a polynomial and writes in in the divided power basis,
    --where a^(n) is represented as a^n.
    S := ring p;
    sub0 := map(S,S,0_S*vars S);
    (monoms, coeffs) := coefficients p;
    D := sub0 diff(monoms, transpose monoms);
    (flatten entries (monoms*D*coeffs))_0
)

toDividedPowers Matrix := M -> (
    --same for all the entries of a matrix
    map(target M, source M, (i,j) -> toDividedPowers (M_j_i))
)


fromDividedPowers = method()
fromDividedPowers RingElement := p -> (
    --fromDividedPowers takes a polynomial written in the divided power basis,
    --where a^(n) is represented as a^n,
    --and changes it to a polynomial written in the monomial basis.
    S := ring p;
    sub0 := map(S,S,0_S*vars S);
    (monoms, coeffs) := coefficients p;
    D := sub0 diff(monoms, transpose monoms);
    (flatten entries (monoms*(inverse D)*coeffs))_0
)
fromDividedPowers Matrix := M -> (
    --same for all the elements of a matrix
    map(target M, source M, (i,j) -> fromDividedPowers (M_j_i))
)


--fromDual takes a matrix or ring element and returns an ideal.
fromDual = method(Options=>{DividedPowers => true, PowerBound => 0})						  

fromDual Matrix := o -> M -> (
     	  if not isStandardGradedPolynomialRing ring M then 
 	     error"Requires base ring to be a standard graded polynomial ring over a field";
    	  if numgens target M > 1 then error"Input matrix has too many rows.";
	  M' := compress M;
 	  --handle the case when the input was 0:
 	  if numgens source M' == 0 then return matrix{{1_(ring M)}};
	  dtar :=  (degrees target M)_0_0;	  
	  R := ring M;
	  v := gens R;
	  if o.DividedPowers === false then M' = toDividedPowers M';
	  dmax := o.PowerBound;
	  if dmax == 0 then
    	  dmax = (max apply (flatten entries M', f->(degree (f))))_0;
          g := matrix{{product powers(dmax, v)}};
          I1 := ideal contract(transpose M', g);
	  I := (ideal powers(dmax+1, v) : I1);
	  if isHomogeneous I then I = trim I;
	  gens I
	  )	  
fromDual RingElement := o -> f -> fromDual(matrix{{f}}, DividedPowers=> o.DividedPowers)


powers = (d,v) ->
   -- v a list of ring elements; d a natural number. Returns the list of powers.
    apply(v, x->x^d)

    
containsDthPowers = method()
containsDthPowers Ideal := I->(
    --input is an ideal of dimension 0.
    --returns the smallest d such that I contains the d-th 
    --powers of all the variables.
    if dim I != 0 then error"Input ideal must be 0-dimensional";
    S := ring I;
    v := gens S; -- a list
    n := numgens S;
    d := min flatten degrees I;
    while (matrix{powers(d,v)} % I) != 0 do d = d+1;
    d
   ) 


toDual = method(Options => {DividedPowers => true})
toDual (ZZ,Ideal) := o -> (d,I) -> (
         -- assumes that I is an ideal in a polynomial ring
	 -- returns a matrix representing the annihilator of I in the dual of ring I, accurate up to dual degree d.
         S := ring I;
    	  if not isStandardGradedPolynomialRing S then 
	     error"Base ring should be a standard graded polynomial ring over a field";
         g := product powers(d,gens S);
	 box :=ideal powers(d+1,gens S);
         m := compress contract(gens(box : I) % box, matrix{{g}});
	 if o.DividedPowers === false then m = fromDividedPowers m;    
    	 m
    )
--the following is added to imitate the (illogical) behavior of the old toDual
toDual (ZZ, Matrix) := o->(d,M) -> toDual(d, ideal M)


inverseSystem = method(Options => {DividedPowers => false, PowerBound => 0})
inverseSystem Ideal := o-> I -> (
    d := o.PowerBound; -- this is potentially less than the regularity. Is this ok??
    if d===0 then
     if 0==dim I then d = 1+containsDthPowers I
     else return "ideal not zero-dimensional; needs explicit option PowerBound.  
     Re-run as 
     inverseSystem(I, PowerBound => D)
     for appropriate D.";
    toDual(d,I,DividedPowers => o.DividedPowers)
    )

inverseSystem Matrix := o-> M -> (
    ideal fromDual(M, DividedPowers => o.DividedPowers)
    )

inverseSystem RingElement := o-> M -> (
    ideal fromDual(M, DividedPowers => o.DividedPowers)
    )

contractInDegree = method()
contractInDegree (ZZ, RingElement) := Matrix => (i, phi) -> (
    if not isHomogeneous phi then (error "Expected a homogeneous polynomial.");
    D := ring phi;
    d := (degree phi)#0;
    --if i > d or i < 0 then (error "Expected a non-negative integer no bigger than the degree of the polynomial.");
    if i > d or i < 0 then return map((coefficientRing D)^(binomial(d-i+(numgens D)-1,d-i)),(coefficientRing D)^(binomial(i+(numgens D)-1,i)),0);
    matrix apply(flatten entries super basis(d - i, D), 
	m -> apply(flatten entries super basis(i, D),
	    u -> coefficient(m, contract(u, phi))
	    )
	)
    )

contractInDegree (ZZ, List) := Matrix => (i, L) -> (
    if any (L,phi -> not isHomogeneous phi) then (error "Expected a list of homogeneous polynomials.");
    D := ring L#0;
    if any (L,phi->ring phi =!= D) then (error "Expected polynomials in the same ring.");
    if L=={} then return map((coefficientRing D)^1, (coefficientRing D)^0,0);
    s := flatten (L/degree);
    d := max s;
    if i > d or i < 0 then return map((coefficientRing D)^(binomial(d-i+(numgens D)-1,d-i)),(coefficientRing D)^(binomial(i+(numgens D)-1,i)),0);
    matrixList := apply(#s,j -> contractInDegree(i,L#j));
    concatMatrix := matrixList#0;
    matrixList = remove(matrixList,0);
    while matrixList =!= {} do (
	concatMatrix=concatMatrix || matrixList#0; 
	matrixList = remove(matrixList,0)
	);
    concatMatrix
    )

contractKernelInDegree = method()

contractKernelInDegree (ZZ, RingElement) := Ideal => (i,phi) -> (
    I := inverseSystem(matrix{{phi}},DividedPowers=>true);
    super basis(i,I)
    )

contractKernelInDegree (ZZ, List) := Ideal => (i,L) -> (
    if any(L, phi -> not isHomogeneous phi) then (error "Expected a list of homogeneous polynomials.");
    I := inverseSystem(matrix{L},DividedPowers=> true);
    super basis(i,I)
    )
 
 contractImageInDegree = method()

contractImageInDegree (ZZ, RingElement) := Ideal => (i,phi) -> (
    R := ring phi;
    ideal contract(symmetricPower(i,vars R),phi)
    )

contractImageInDegree (ZZ, List) := Ideal => (i,L) -> (
    R := ring L#0;
    apply(L,phi -> ideal contract(symmetricPower(i,vars R),phi))
    )
   

{*
dividedImInDegree = method()
dividedImInDegree (ZZ, RingElement) := Ideal => (i, phi) -> (
    I := contractInDegree(i, phi);
    D := ring phi;
    d := (degree phi)#0;
    ideal mingens ideal( (super basis(d-i, D)) * I )
    )

dividedImInDegree (ZZ, List) := Ideal => (i, L) -> (
    s := flatten (L/degree);
    d := max s;
    apply(L,phi->(dividedImInDegree(i,phi)))
    )

dividedImInDegree (ZZ, Matrix) := Ideal => (i, A) -> (
    D := ring A;
    n := numgens D;
    d := 0;
    while binomial(d-i + n -1, n-1) < numrows A do(
	d = d + 1
	); 
    if i > d or i < 0 then (error "Expected a non-negative integer no bigger than the degree of the polynomial.");
    ideal mingens ideal( (super basis(d - i, D) * A) )
    )
*}

beginDocumentation()


doc ///
Key
 InverseSystems
Headline
 Macaulay's Inverse Systems
Description
 Text
  The graded Hopf algebra dual of the symmetric algebra
  $S := k[x_1,\dots,x_n]$ is the divided power algebra
  $D$. The dual basis to the monomial basis of $S$
  is the basis consisting of monomials
  $x_1^{(m_1)} \dots x_n^{(m_n)}$ and multiplication
  (for example). In characteristic zero,
  $S$ and $D$ are isomorphic as algebras, with 
  isomorphism sending 
  $x_i^{a}$ to $a!x_i^{(a)}$.
  In general the multiplication in $D$ is defined
  by the same formulas as in characteristic 0.
  For example,

  $x_1^{(1)}*x_1^{(1)} = 2*x_1^{(2)}$.

  In finite characteristic $D$ and $S$ are not isomorphic; $D$ is not even
  a finitely
  generated algebra. 
  
  We will be interested
  also in the local versions, where we take power series
  in the divided powers. This is the ordinary linear dual of $S$.
  We denote it by
  $D'$. When regarded as an $S$-module $D'$ is
  thus the injective hull of the simple module
  $S/(x_1,\dots,x_n)$.  
  
  Since $D$ is the graded dual of $S$, it may also be regarded as an
  $S$-module as such, any element of $D$ is annihilated by a power
  of $mm = (x_1,\dots,x_n)$, so the action of $S$ on 
  $D$ or $D'$ factors through
  the localization $S'$ of $S$ at $mm$.
  
  The inverse system of an $S'$-submodule M of $D'$ is
  the annihilator I of M in $S'$ (or in $S$).  If $M$ is finitely
  generated then it is annihilated by some power of $mm$,
  and thus I is 0-dimensional.
  
  Inversely, the (local) inverse system of an ideal in $S$
  or $S'$ is
  by definition the submodule of $D'$ it annihilates.
  
  In the 1880's these ideas were used by Max Noether, in the
  local version, as a substitute for primary decomposition in the 
  case of what he called multiple points in the plane. 
  F. S. Macaualay studied and greatly refined Noether's
  work, and for example identified the ideals I that are
  annihilators of cyclic submodules of $D'$ as the ideals
  such that one could do residuation in $S'/I$ -- 
  that is, $S'/I$ is Gorenstein.
  Though the global version
  has also been studied (see Emsalem [****]), we will only
  be concerned with the local version. 
  
  Any 
  finitely generated submodule of D' generated by finite
  polynomials is actually a submodule of D, and its dual
  will have only primary components contained in
  $(x_1,\dots,x_n)$ so the distinction
  will not be important for us on that side. 
  However, it is imporant
  to note that when taking the inverse system of an ideal,
  only the primary components contained in 
  $(x_1,\dots,x_n)$ play a role.

  %%%%%%%%%%%%%%%%%%%%%%%%  

  Going from a submodule of D to an ideal of $S$: 
  
  Because D and D' are not finitely generated S-modules
  Macaulay2 cannot deal with them directly.
  These scripts can only deal with a finitely generated 
  submodule M of D or D'. Such a module is represented here
  by a row matrix, of
  ordinary polynomials, whose entries are thought of as
  generators of M. 
  
  In the default behavior
  of the script
  
  inverseSystem M = inverseSystem(M, DividedPowers => false)
  
  a monomial $x^a$ is taken to represent
  $a!x^{(a)} \in D'$, where, if
  $a = (a_1,\dots,a_n)$, then $a! = a_1!*\dots*a_n!$.
  This means
  that the script should not be used in the default
  way unless the characteristic is greater than the highest
  degree to which a variable appears. 
  
  To make $x^a$ represent $x^(a)$,
  for example in small characteristics use
  
  inverseSystem(Matrix, DividedPowers=>true)
  
  (which was the default behavior of the old script
  "fromDual"). 

  The reason for the default choice is that the
  general linear group GL_n(k) acts on both S and D, and
  it is reasonable to expect that the operations
  defined by inverseSystem should be equivariant. This is
  the case for the default setting, but with
  DividedPowers=>true it is not the case:
  for example, 
 Example
  S = QQ[x,y]
  J = inverseSystem x^2
  I = inverseSystem(x^2, DividedPowers=>true)
  I == J
  betti res I
 Text
  is equivalent to the ideal
 Example
  J' = inverseSystem (x+y)^2
 Text
  but very different from the ideal
 Example
  I' = inverseSystem(matrix{{(x+y)^2}}, DividedPowers=>true)  
  betti res I'
 Text
 
  Indeed, in the default behavior inverseSystem is equivariant in a precise sense:
  If G is an $n\times n$ invertible scalar matrix, then G defines an automorphism 
  g: S\to S by change of variables. Also g also acts on 1 x m matrices M, componentwise, and,
  with the default behavior of inverseSystem (that is, DividedPowers=>false) we have
  (transpose g)^{-1} (inverseSystem M) = inverseSystem(g M), as illustrated below:
 Example
  kk = QQ
  n = 3
  S = kk[a,b,c]
  M = matrix{{a^2,b^3+c^3}}
 
  G = random(S^3, S^3)
  g = map(S,S,(vars S)*G)
  g' = map(S,S,(vars S)*(transpose G))
  h =  map(S,S,(vars S)*(transpose G)^(-1))

  inverseSystem M
  g'(inverseSystem g(M))
 Text
  These may look different, but...
 Example
  g'(inverseSystem g(M)) == inverseSystem M
 Text
  Equivalently,
 Example
  h(inverseSystem M) == inverseSystem g(M)
		
 Text  
  There is a similar equivariance for the dual action of inverseSystem on ideals.

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
  Going from an ideal of S to a submodule of D:
  
  If $I$ is an ideal of $S$, homogeneous or not,
  we regard $I$ as an ideal of $S'$. If $S'/I$ is of
  finite length then
  
  M = inverseSystem I
  M1 = inverseSystem(I, DividedPowers => true)
  
  both return 1 x m matrices whose entries are
  the minimal generators of
  the annihilator of $I$ in $D'$. In the matrix $M$
  a term $x^a$
  is to be interpreted as 
  $a! x^(a)$, while in the matrix $M1$ it is interpreted
  as $x^(a)$. Of course the first computation is only
  valid if all the powers of variables appearing in the generators
  of $I$ are < char k.
  
  On the other hand, if $S/I$ is not of finite length, then the
  optional argument PowerBound is mandatory, and
 
  M = inverseSystem(I, PowerBound => d)
  M1 = inverseSystem(I, DividedPowers => true, PowerBound => d)

  will compute as above but with results valid only up to degree d.
  
  To represent finitely generated S-submodule of $D'$
  as an S-module we use the map of modules
  D'-> S/(x_1^d,\dots, x_n^d) sending $x^{(a)}$ to 
  contract(x^a, product(n, j-> x_i^{d-1})), 
  which we treat as being defined only when the variables
  in $x^{(a)}$ appear only with powers < d.
  
Caveat
 The translations used involve multiplying or dividing by scalars; if the polynoimials
 involved have maximum degree n, then n! must be invertible for the translation to make sense.
SeeAlso
 inverseSystem
 fromDual
 toDual
 PowerBound
 DividedPowers
 fromDividedPowers
 toDividedPowers
 
///

doc ///
Key
 inverseSystem
 (inverseSystem, Ideal)
 (inverseSystem, Matrix)
 (inverseSystem, RingElement) 
 [inverseSystem,DividedPowers] 
 [inverseSystem,PowerBound]  
Headline
 Inverse systems with equivariance. Can replace fromDual and toDual
Usage
 I1 = inverseSystem M
 M1 = inverseSystem I
Inputs
 M:Matrix
 M:RingElement
 I:Ideal
Outputs
 I1:Ideal
 M1:Matrix
Description
 Text
  Let S = k[x_1..x_n] be a standard graded polyomial ring,
  and let D be its dual, the divided power algebra,
  regarded as an S-module.  Let M be a 1xm matrix of polynomials,
  and let I be an ideal of S. 
  
  From a submodule of D to an ideal of S:
  
  We think of the entries of M as generators of an  S-submodule MM of D,
  and 
  inverseSystem M returns the annihilator in S of MM.
  In the default behavior
  a monomial $x^a$ in an entry of the matrix M is taken to represent
  $a!x^(a) \in D'$, where,
  $a = (a_1,\dots,a_n)$ then $a! = a_1!*\dots*a_n!$. Use
  
  inverseSystem(M, DividedPowers => false)
  
  to make the monomials of entries of M represent the dual basis of the monomial basis of S,
  that is, the divided powers of the generators of D as an algebra.
  
  From an ideal of S to a submodule of D:
  
  If $I$ is an ideal of $S$, homogeneous or not,
  we regard $I$ as an ideal of the localization $S'$ of $S$ at $(x_1,\dots,x_n)$. If $S'/I$ is of
  finite length then
  
  M = inverseSystem I
  
  and
  
  M1 = inverseSystem(I, DividedPowers => false)
  
  each return a 1 x m matrix whose entries are
  the minimal generators of
  the annihilator of $I$ in $D$. In the matrix $M$
  a term $x^a$
  is to be interpreted as 
  $a! x^(a)$, while in the matrix $M'$ it is interpreted
  as $x^(a)$. Of course the first computation is only
  valid if all the powers of variables appearing in the generators
  of $I$ are < char k.
  
  On the other hand, if $S/I$ is not of finite length, then the
  optional argument PowerBound is mandatory, and
 
  M = inverseSystem(I, PowerBound => d)
  M1 = inverseSystem(I, DividedPowers => false, PowerBound => d)

  will compute as above but with results valid only up to degree d.
  
  To make these computations it is necessary to represent some sufficiently
  large finitely generated S-submodule of $D$ (this will automatically be
  an $S'$-submodule. To do this we use the map of modules
  D-> S/(x_1^d,\dots, x_n^d) sending $x^{(a)}$ to 
  contract(x^a, product(n, j-> x_i^{d-1})), defined only when the variables
  in $x^{(a)}$ appear only with powers < d.
  
 Example
  setRandomSeed 0
  kk = QQ
  S = kk[a,b,c]
  map(S,S,0_S*vars S)
  p = (a+b)^2
  q = toDividedPowers p
  p' = fromDividedPowers q
  p'==p
 Text
  Here are some codimension 4 Gorenstein rings with different Betti tables,
  computed by inverseSystem
  from quartic polynomials
 Example
  kk = ZZ/101
  S = kk[a..d]

  f1 = matrix"a2b2+c2d2"; -- gives 1,4,6,4,1
  f2 = matrix"a2b2+b2c2+c2d2"; --gives 1,4,7,4,1;
  f3 = matrix"a2b2+b2c2+c2d2+c2a2"; -- gives 1,4,8,4,1
  f4 = matrix"a2b2+b2c2+c2d2+c2a2+a2d2"; --gives 1,4,8,4,1
  f5 = matrix"a2b2+b2c2+c2d2+c2a2+a2d2+b2d2+b4"; --gives 1,4,9,4,1
  f6 = matrix"a2b2+b2c2+c2d2+c2a2+a2d2+b2d2"; --gives 1,4,10,4,1
  F = {f1,f2,f3,f4,f5,f6};
  netList (F/(f->betti res inverseSystem f))

Caveat
 Because inverseSystem
 involves a conversion between the bases of the dual,
 it should not be used in the default mode
 unless the characteristic is greater than the highest
 degree to which a variable appears. 
 To make $x^a$ represent $x^(a)$,
 for example in small characteristics use
  
 inverseSystem(Matrix, DividedPowers=>false)
  
 (which was the default behavior of the old script
 "fromDual"). 
SeeAlso
 DividedPowers
 PowerBound
 fromDividedPowers
 toDividedPowers
 fromDual
 toDual
 isStandardGradedPolynomialRing
 contractInDegree
 contractKernelInDegree
 contractImageInDegree
///

doc ///
   Key
    DividedPowers
   Headline
    Option for inverseSystem
   Description
    Text
   Caveat
   SeeAlso
    inverseSystem
///
doc ///
   Key
    PowerBound
   Headline
    Option for inverseSystem
   Description
    Text
   Caveat
   SeeAlso
    inverseSystem
///

doc ///
   Key 
    fromDividedPowers
    (fromDividedPowers,Matrix)
    (fromDividedPowers,RingElement)
   Headline 
    Translates from divided power monomial basis to ordinary monomial basis
   Usage
    f1 = fromDividedPowers f
   Inputs
    f:RingElement
    f:Matrix
   Outputs
    f1:RingElement
    f1:Matrix
   Description
    Text
     If f is a polynomial, or a matrix of polynomials, written in the divided power monomial basis, then f1 is the corresponding
     object written in the ordinary monomial basis.
    Example
     S = ZZ/101[x,y]
     x^2 == fromDividedPowers (2*x^2)
   SeeAlso
    toDividedPowers
///
doc ///
   Key 
    toDividedPowers
    (toDividedPowers,Matrix)
    (toDividedPowers,RingElement)
   Headline 
    Translates to divided power monomial basis from ordinary monomial basis
   Usage
    f1 = toDividedPowers f
   Inputs
    f:RingElement
    f:Matrix
   Outputs
    f1:RingElement
    f1:Matrix
   Description
    Text
     If f is a polynomial, or a matrix of polynomials, then f1 is the corresponding
     object written in the divided power monomial basis, where for example $x^2$ denotes $x^{(2)}$
    Example
     S = ZZ/101[x,y]
     2*x^2 == toDividedPowers (x^2)
   SeeAlso
    fromDividedPowers
///

doc ///
   Key
    toDual
    (toDual, ZZ,  Ideal)
    (toDual, ZZ, Matrix)
    [toDual,DividedPowers]
   Headline
    finds the inverse system to an ideal up to a given degree
   Usage
    M = toDual (ZZ, I)
   Inputs
    I:Ideal
     in a standard graded polynomial ring
   Outputs
    M:Matrix
     interpreted as list of generators of inverse system to I
   Description
    Text
     If I is an ideal, then toDual(d,I) = inverseSystem(I, PowerBound =>d). 
     See the documentation of
     InverseSystems for the basic theory and of inverseSystem for the function.
     
     If I is a matrix, then the code first replaces it with the ideal generated by the entries.
   Caveat
    The Base ring of the input must be a standard graded polynomial ring over a field.
   SeeAlso
    InverseSystems
    inverseSystem    
    fromDual
///
doc ///
   Key
    fromDual
    (fromDual, RingElement)
    (fromDual, Matrix)
    [fromDual,PowerBound]
    [fromDual,DividedPowers]
   Headline
    Ideal from inverse system
   Usage
    M  = fromDual f
   Inputs
    f:Matrix
     with one row
    f:RingElement
   Outputs
    M:Matrix
     interpreted as the generators of an ideal
   Description
    Text
     The matrix (or ring element) f is interpreted as an element of the linear dual of
     the base polynomial ring, where the monomial in f are interpreted as monomials in the 
     divided power basis (the dual basis of the monomial basis of ring f. Thus
	 
     fromDual f = gens inverseSystem (f, DividedPowers => true).

     See the documentation nodes for InverseSystems for the theory, and inverseSystem for
     the function. Note that the operation of fromDual is not equivariant with respect
     to the general linear group, acting by change of basis. This not a bug, but
     follows because fromDual
     uses the divided power basis. If equivariant behavior is desired, use
     the option DividedPowers=>false, which is the default behavior of 
     inverseSystem:
    Example
     S = ZZ/101[x,y]
     f1 = x^2
     f2 = (x+y)^2
     betti res ideal fromDual f1
     betti res ideal fromDual f2
     betti res (I = ideal fromDual(f2, DividedPowers => false))
     I == inverseSystem f2
   Caveat
    The Base ring of the input must be a standard graded polynomial ring over a field.

    Logically, the output of fromDual should be an ideal, not a matrix, but the original
    function was converted from the classic Macaulay, where this distinction was not made.
   SeeAlso
    InverseSystems
    inverseSystem    
    fromDual
///
doc ///
   Key
    isStandardGradedPolynomialRing
    (isStandardGradedPolynomialRing, Ring)
   Headline
    Checks whether a ring is a polynomial ring over a field with variables of degree 1
   Usage
    b = isStandardGradedPolynomialRing R
   Inputs
    R:Ring
   Outputs
    b:Boolean
   SeeAlso
    isPolynomialRing
///  

doc ///
   Key
    contractInDegree
    (contractInDegree, ZZ, RingElement)
    (contractInDegree, ZZ, List)
   Headline
    Computes the contraction with an element of the divided powers algebra in a given degree
   Usage
    M = contractInDegree(i, phi)
    M = contractInDegree(i, L)
   Inputs
    i: ZZ
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous polynomials in a standard graded polynomial ring 
   Outputs
    M: Matrix
   Description 
    Example
     S = ZZ/5[x,y,z]
     phi = x^5*y^2 + y^5*z^2 + z^5*x^2
     contractInDegree(3, phi)
   SeeAlso
    contract
     ///
{*     
doc ///
   Key
    dividedKerInDegree
    (dividedKerInDegree, ZZ, RingElement)
    (dividedKerInDegree, ZZ, List)
    (dividedKerInDegree, ZZ, Matrix) 
   Headline
    Computes the kernel of the action of homogeneous polynomials on elements of the divided powers algebra in a given degree
   Usage
    I = dividedKerInDegree(i, phi)
    I = dividedKerInDegree(i,L)
    I = dividedKerInDegree(i,A)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
    A: Matrix
     the output matrix from dividedActionInDegree(i,phi) or dividedActionInDegree(i,L)
   Outputs
    I: Ideal
   Description
    Text
     Computes the degree i piece of the kernel of the map from symmetric powers to divided powers 
     given by multiplication by the ring element or list of elements. Matrix option allows user to
     input matrix gotten from dividedActionInDegree function, to avoid having to repeat the computation.
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     psi = dividedKerInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3,y^3,z^3,x*y^2+y*z^2,z*x^2}
     psi = dividedKerInDegree(i,L)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     A = dividedActionInDegree(i,phi)
     psi = dividedKerInDegree(i,A)
     ///
*}

doc ///
   Key
    contractKernelInDegree
    (contractKernelInDegree, ZZ, RingElement)
    (contractKernelInDegree, ZZ, List)
   Headline
    Computes the kernel of the action of homogeneous polynomials on elements of the divided powers algebra in a given degree
   Usage
    I = contractKernelInDegree(i, phi)
    I = contractKernelInDegree(i,L)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
   Outputs
    I: Ideal
   Description
    Text
     Computes the degree i piece of the kernel of the map from symmetric powers to divided powers 
     given by multiplication by the ring element or list of elements. 
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     psi = contractKernelInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3,y^3,z^3,x*y^2+y*z^2,z*x^2}
     psi = contractKernelInDegree(i,L)
     ///

{*
doc ///
   Key
    dividedImInDegree
    (dividedImInDegree, ZZ, RingElement)
    (dividedImInDegree, ZZ, List) 
    (dividedImInDegree, ZZ, Matrix)
   Headline
    Computes the image of the action of homogeneous polynomials on elements of the divided powers algebra in given degrees
   Usage
    U = dividedImInDegree(i, phi)
    W = dividedImInDegree(i, L)
    U = dividedImInDegree(i, A)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
    A: Matrix
     the output matrix from dividedActionInDegree(i,phi) or dividedActionInDegree(i,L)
   Outputs
    U: Ideal
     an ideal whose generators span the image
    W: List
     a list of ideals
   Description
    Text
     Computes the image of the map from the ith graded piece of the symmetric algebra to the direct sum of 
     divided power rings, which is given by multiplication by the ring element or list of elements. 
     The Matrix option allows the user to input the matrix gotten from dividedActionInDegree function, 
     to avoid having to repeat the computation.
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     U = dividedImInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3+y^3+z^3,x*y^2+y*z^2+z*x^2}
     W = dividedImInDegree(i,L)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     A = dividedActionInDegree(i,phi)
     U = dividedImInDegree(i,A)
     ///
*}

doc ///
   Key
    contractImageInDegree
    (contractImageInDegree, ZZ, RingElement)
    (contractImageInDegree, ZZ, List)
   Headline
    Computes the image of the action of homogeneous polynomials on elements of the divided powers algebra in a given degree
   Usage
    I = contractImageInDegree(i, phi)
    I = contractImageInDegree(i,L)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
   Outputs
    I: List
     a list of ideals
   Description
    Text
     Computes the image of the map from the ith symmetric power to divided powers 
     given by multiplication by the ring element or list of elements. 
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     psi = contractImageInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3,y^3,z^3,x*y^2+y*z^2,z*x^2}
     psi = contractImageInDegree(i,L)
     ///

  
TEST ///

S = ZZ/5[x,y,z]; 
phi = x^3+y^3+z^3;
assert(contractInDegree(2,phi)==matrix(ZZ/5,{{1,0,0,0,0,0},{0,0,0,1,0,0},{0,0,0,0,0,1}}))
assert(contractKernelInDegree(2, phi)==ideal(x*y,x*z,y*z))
assert(contractImageInDegree(2, phi)==ideal(x,y,z))

///


TEST ///

R=ZZ/5[x,y,z];
I=ideal(x^3+y^3+z^3,x*y^2+y*z^2+z*x^2);
assert(contractInDegree(2,I_*)==matrix(ZZ/5,{{1,0,0,0,0,0},{0,0,0,1,0,0},{0,0,0,0,0,1},{0,0,1,1,0,0},{0,1,0,0,0,1},{1,0,0,0,1,0}}))
assert(contractKernelInDegree(2,I_*)==ideal(0_R))
assert(contractImageInDegree(2,I_*)=={ideal(x,y,z),ideal(x,y,z)})

///







--check that the bounds are right
TEST///
S= QQ[a,b,c]
d= 3
f = product(3,i->S_i^(d-1))
I = ideal apply(3, i->S_i^d)
assert(I == inverseSystem f)
assert (I == inverseSystem inverseSystem I)
///

TEST///
R = ZZ/101[a,b]
assert(isStandardGradedPolynomialRing R)
assert(not isStandardGradedPolynomialRing (R[x]))
assert(not isStandardGradedPolynomialRing (ZZ[x]))
assert(not isStandardGradedPolynomialRing (R[x, Degrees =>{{1,1}}]))
///       

--fromDividedPowers and toDividedPowers are inverse to one another
TEST///
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
p = (a+b)^2
q = toDividedPowers p
assert(q == 2*a^2+2*a*b+2*b^2)
assert(p ==fromDividedPowers q)

P = (random(S^{0,1},S^{-2,-3}))
Q = fromDividedPowers toDividedPowers P
R = toDividedPowers fromDividedPowers P
assert(P==Q)
assert(P == R)

setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
g == fromDividedPowers toDividedPowers g
g == toDividedPowers fromDividedPowers g
///

--with or without divided powers,
--applying inverseSystem twice should be 
--the identity on ideals AND on submodules of the dual, represented as matrices.
TEST///
setRandomSeed 0
S = QQ[a,b]
G = random(S^2,S^2)
GG = map(S,S,(vars S)*G)
GG' = map(S,S,(vars S)*transpose G^-1)
f = a^2
g = b^3
h = GG matrix{{f,g}}
I = ideal h
--the equality for ideals:
assert(I ==  inverseSystem inverseSystem(I,PowerBound =>4))
assert(I ==  inverseSystem(inverseSystem(I, PowerBound=>4, DividedPowers=>true), 
			   DividedPowers =>true
			  )
       )
--The equality for matrices 
--since we can't directly compare submodules of the injective hull, we compare them by taking their annihilators:
assert(inverseSystem h == inverseSystem inverseSystem(inverseSystem h, PowerBound=>4))
assert(inverseSystem h == inverseSystem(inverseSystem(inverseSystem h, PowerBound=>4, DividedPowers=>true), 
	                                DividedPowers=>true))
///

--inverseSystem is equivariant on matricses
TEST///
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
assert(inverseSystem matrix{{0_S}} == ideal(1_S))

g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
testmap' = map(S,S,(vars S)*(dual g)^-1)

f = matrix{{a,b^3}}
assert(testmap' inverseSystem f == 
       inverseSystem (testmap f)
		)
f = random(S^1, S^{-2,-2,-3})
assert(testmap' inverseSystem f == 
       inverseSystem (testmap f)
		)
///

--inverseSystem is equivariant on 0-dimensional ideals 
--(and, up to the given degree, on arbitrary ideals)
TEST///
setRandomSeed 0
kk = QQ
n = 3
S = kk[a,b,c]
g = random(S^3, S^3)
testmap = map(S,S,(vars S)*g)
testmap' = map(S,S,(vars S)*(dual g)^-1)

f = random(S^1, S^{-2,-2,-3});
assert(inverseSystem testmap' inverseSystem f == 
       inverseSystem inverseSystem (testmap f)
		)
f = ideal(a,b^3)+(ideal vars S)^4;
assert( inverseSystem testmap'  inverseSystem (f, PowerBound => 4) == 
       inverseSystem inverseSystem (testmap f, PowerBound => 4)
		)

mm=ideal vars S
f = ideal(a,b^3)
f = ideal random(S^1, S^{-2,-3});
assert(mm^5+inverseSystem testmap'  inverseSystem (f, PowerBound => 4) == 
       mm^5+inverseSystem inverseSystem (testmap f, PowerBound => 4)
		)
///

TEST///
--the local, that is, inhomogeneous case:
S = QQ[a,b,c]
G = random(S^3,S^3)
GG = map(S,S,(vars S)*G)
M = matrix{{a^2+b^3}}
I1 = inverseSystem M
I2 = inverseSystem GG M
assert(hilbertSeries ideal leadTerm gens gb I1===hilbertSeries ideal leadTerm gens gb I2)

S = QQ[x,y]
I = ideal"x3,xy+y4+y5"+(ideal vars S)^7
M' = inverseSystem I
assert(I ==inverseSystem M')

M'' = inverseSystem(I,DividedPowers => true)
assert(I ==inverseSystem (M'',DividedPowers => true))

assert(M'!= M'')
---
S = QQ[x,y]
I = ideal"x3,xy+y4+y5"+(ideal vars S)^7
M' = inverseSystem I
assert(I ==inverseSystem M')

M'' = inverseSystem(I, DividedPowers => true)
assert(I ==inverseSystem (M'',DividedPowers => true))

assert(M'!= M'')
///

     -- a test from the old documentation
     TEST ///
     	  R = ZZ/32003[a..e];
	  f = matrix{{a^2, b^2, c^2, d^2, e^3, a*d-e^2}}
	  g = toDual(1,f)
	  ideal fromDual g == ideal f
	  g = toDual(2,f)
	  ideal fromDual g == ideal f
	  g = toDual(3,f)
	  ideal fromDual g == ideal f
	  ///

TEST ///
 R = QQ[a,b,c]
 f= matrix"a-b,c"
 toDual(1,f)
 toDual(2,f)
 toDual(3,f)
///

document {
     Key => "inverse systems",
     "Suppose that R = k[x1,...,xn], and that
     E = k[y1,...,yn] is the injective envelop of k.  IE, E is given the R-module structure:
     x^A . y^B = y^(B-A), if B-A >= 0 in every component, and x^A . y^B = 0 otherwise.",
     PARA{},
     "If I is an ideal of R, then the submodule I' = Hom_R(R/I,E) of E is called the
     (Macaulay) inverse system of I.  I is zero-dimensional if and only if I' is finitely generated.",
     PARA{},
     "This is a dual operation, since I can be recovered as ann_R(I').",
     PARA{},
     "In Macaulay2, currently the computation of the inverse system I' (toDual) and of the 
     ideal I from I' (fromDual) are restricted to the situation where I and I' are homogeneous.
     As an example, let's compute the ideal corresponding to a cubic.",
     EXAMPLE lines ///
     	 R = QQ[a..e];
	 g = matrix{{a^3+b^3+c^3+d^3+e^3-d^2*e-a*b*c-a*d*e}}
	 f = fromDual g
	 I = ideal f
	 ///,
     "The resulting ideal is always zero dimensional, and its Cohen-Macaulay type is the
     number of generators of the submodule E defined by g.  Therefore, if g is a 1 by 1 matrix,
     then the resulting ideal is Gorenstein.",
     EXAMPLE lines ///
	 res I
	 betti oo
         ///,
     PARA{},
     "The other direction (starting with an ideal I) is more complicated, since the result may not be finitely generated.
     So, we must give an integer d as well as the generators of I:",
     EXAMPLE lines ///
     	 toDual(3,f)
         ///,
     "The integer d has two interpretations.  The most general is that the (finitely generated)
     intersection of I' and the submodule generated by y1^d ... yn^d is returned.
     If the ideal I is zero dimensional, d should be an integer such that x^(d+1) is in I = image f for 
     every variable x.",
     EXAMPLE lines ///
         f = matrix{{a*b,c*d,e^2}}
	 toDual(1,f)
	 toDual(2,f)
	 toDual(3,f)
	 g = toDual(4,f)
	 fromDual g
	 ///,
     SeeAlso => {toDual, fromDual}
     },
     
     -- a test from the old documentation
     TEST ///
          R = ZZ/32003[x_1..x_3];
	  g = random(R^1, R^{-4})
	  f = fromDual g
	  res ideal f
	  betti oo
          ///

TEST ///
    R = ZZ/101[a..d]
    f = matrix{{a^3 + b^3 + c^3 + d^3 + (a+b+c)^3}}
    fdual = fromDual f
    assert(f - toDual(4, fdual) == 0)
///

end--
restart
loadPackage("InverseSystems", Reload =>true)
uninstallPackage("InverseSystems")
installPackage("InverseSystems")
check "InverseSystems"
viewHelp InverseSystems

cubic = (g,r) -> (
    --make the sum of r cubes in g-2 variables
    x := symbol x;
    S := ZZ/101[x_0..x_(g-3)];
    sum(r, i-> if i<=g-3 then x_i^3 else ((random(S^1,S^{-1}))_0_0)^3)
    )
cubic(6,3)
betti res inverseSystem cubic(6,5)

g= 9
netList apply(toList(g-2..2*g-4), j-> betti res inverseSystem cubic(g,j))
