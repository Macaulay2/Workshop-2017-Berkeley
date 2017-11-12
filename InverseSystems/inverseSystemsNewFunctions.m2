needsPackage "InverseSystems"

lowerExponent = method()

lowerExponent (RingElement, List) := RingElement => (phi,l) -> (
    D := ring phi;
    if not isStandardGradedPolynomialRing D then (error "Expected a polynomial in a standard graded polynomial ring.");
    if not #l == numgens D then (error "Expected the length of the list to be equal to the number of variables.");
    if any(l, i -> not instance(i, ZZ) or i < 0) then (error "Expected a list of non-negative integers.");
    expList := exponents(phi);
    expList = select(expList, e->all(e-l,i->(i>=0)));
    sum(apply(expList,e->coefficient(D_e,phi)*D_(e-l)))
    )

--Input: A polynomial 'phi' representing an element of a divided powers algebra and a list 'l' of non-negative integers.
--Output: The polynomial obtained from 'phi' under the action of x^l in the dual polynomial ring.    


lowerExponent (RingElement, RingElement) := RingElement => (phi, f) -> (
    D := ring phi;
    S := ring f;
    if not isStandardGradedPolynomialRing S then (error "Expected a polynomial in a standard graded polynomial ring.");
    if not numgens D == numgens S then (error "Expected the rings of the polynomials to have the same number of variables."); 
    exps := exponents(f);
    coeffs := (coefficients f)_1;
    ((matrix {apply(exps, l -> lowerExponent(phi, l))})*coeffs)_0_0
    )

--Input: A polynomial 'phi' representing an element of a divided powers algebra and a polynomial 'f' in the dual polynomial ring.
--Output: The polynomial obtained from 'phi' under the action of 'f'.
    

-----------------------------------------------------------

dividedActionInDegree = method()

dividedActionInDegree (ZZ, RingElement) := Matrix => (i, phi) -> (
    if not isHomogeneous phi then (error "Expected a homogeneous polynomial.");
    D := ring phi;
    d := (degree phi)#0;
    --if i > d or i < 0 then (error "Expected a non-negative integer no bigger than the degree of the polynomial.");
    if i > d or i < 0 then return map((coefficientRing D)^(binomial(d-i+(numgens D)-1,d-i)),(coefficientRing D)^(binomial(i+(numgens D)-1,i)),0);
    matrix apply(flatten entries super basis(d - i, D), 
	m -> apply(flatten entries super basis(i, D),
	    u -> coefficient(m, lowerExponent(phi, u))
	    )
	)
    )

dividedActionInDegree (ZZ, Ideal) := Matrix => (i, Phi) -> (
    if not isHomogeneous Phi then (error "Expected a homogeneous ideal.");
    D := ring Phi;
    if Phi==0 then return map((coefficientRing D)^1, (coefficientRing D)^0,0);
    gensPhi := flatten entries mingens Phi;
    s := flatten ((flatten entries mingens Phi)/degree);
    d := max s;
    if i > d or i < 0 then return map((coefficientRing D)^(binomial(d-i+(numgens D)-1,d-i)),(coefficientRing D)^(binomial(i+(numgens D)-1,i)),0);
    matrixList := apply(#s,j -> dividedActionInDegree(i,gensPhi#j));
    concatMatrix := matrixList#0;
    matrixList = remove(matrixList,0);
    while matrixList =!= {} do (
	concatMatrix=concatMatrix || matrixList#0; 
	matrixList = remove(matrixList,0)
	);
    concatMatrix
    )

dividedActionInDegree (ZZ, List) := Matrix => (i, L) -> (
    if any (L,phi ->isHomogeneous phi =!= true) then (error "Expected homogeneous polynomials..");
    D := ring L#0;
    if any (L,phi->ring phi =!= D) then (error "Expected polynomials in the same ring.");
    if L=={} then return map((coefficientRing D)^1, (coefficientRing D)^0,0);
    s := flatten (L/degree);
    d := max s;
    if i > d or i < 0 then return map((coefficientRing D)^(binomial(d-i+(numgens D)-1,d-i)),(coefficientRing D)^(binomial(i+(numgens D)-1,i)),0);
    matrixList := apply(#s,j -> dividedActionInDegree(i,L#j));
    concatMatrix := matrixList#0;
    matrixList = remove(matrixList,0);
    while matrixList =!= {} do (
	concatMatrix=concatMatrix || matrixList#0; 
	matrixList = remove(matrixList,0)
	);
    concatMatrix
    )


--Input: A homogeneous polynomial 'phi' representing an element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The matrix representing multiplication by 'phi' on the degree 'i' component of the dual polynomial ring.


-----------------------------------------------------------
    
dividedKerInDegree = method()    
    
dividedKerInDegree (ZZ, RingElement) := Ideal => (i, phi) -> (
    K := gens ker dividedActionInDegree(i, phi);
    D := ring phi;
    ideal mingens ideal( (super basis(i, D)) * K )
    )


dividedKerInDegree (ZZ, Ideal) := Ideal => (i, Phi) -> (
    K := gens ker dividedActionInDegree(i, Phi);
    D := ring Phi;
    ideal mingens ideal( (super basis(i, D)) * K )
    )

dividedKerInDegree (ZZ, List) := Ideal => (i, L) -> (
    K := gens ker dividedActionInDegree(i, L);
    D := ring L#0;
    ideal mingens ideal( (super basis(i, D)) * K )
    )


--Input: A homogeneous polynomial 'phi' representing an element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The kernel of multiplication by 'phi' on the degree 'i' component of the dual polynomial ring.


dividedKerInDegree (ZZ, Matrix) := Ideal => (i, A) -> (
    D := ring A;
    d := 0;
    while binomial(d-i + n -1, n-1) < numrows A do(
	d = d + 1
	); 
    if i > d or i < 0 then (error "Expected a non-negative integer no bigger than the degree of the polynomial.");
    ideal mingens ideal( (super basis(i, D) * A) )
    )

--Input: A matrix 'A' representing multiplication by a homogeneous element of a divided powers algebra on the degree 'i' component of the dual polynomial ring.
--Output: The kernel of multiplication by 'A' in the dual polynomial ring.


-----------------------------------------------------------

dividedKerToDegree = method()

dividedKerToDegree  (ZZ, RingElement) := Ideal => (i, phi) -> (
    if not isHomogeneous phi then (error "Expected a homogeneous polynomial.");
    D := ring phi;
    ideal mingens sum apply(i+1, j -> sub(dividedKerInDegree(j, phi), D))
    )

--Input: A homogeneous polynomial 'phi' representing an element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The kernel of multiplication by 'phi' up to degree 'i' in the dual polynomial ring.

-----------------------------------------------------------

dividedImInDegree = method()

dividedImInDegree (ZZ, RingElement) := Ideal => (i, phi) -> (
    I := dividedActionInDegree(i, phi);
    D := ring phi;
    d := (degree phi)#0;
    ideal mingens ideal( (super basis(d-i, D)) * I )
    )

--in progress
dividedImInDegree (ZZ, Ideal) := Ideal => (i, Phi) -> (
    gensPhi := flatten entries mingens Phi;
    s := flatten ((flatten entries mingens Phi)/degree);
    d := max s;
    apply(gensPhi,phi->(dividedImInDegree(i,phi)))
    )

dividedImInDegree (ZZ, List) := Ideal => (i, L) -> (
    s := flatten (L/degree);
    d := max s;
    apply(L,phi->(dividedImInDegree(i,phi)))
    )


--Input: A homogeneous polynomial 'phi' representing an element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The image of multiplication by 'phi' in the degree of 'phi' - 'i' component in the dual polynomial ring.

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

--Input: A matrix 'A' representing multiplication by a homogeneous element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The image of multiplication by 'A' in the dual polynomial ring.


TEST ///

S = ZZ/5[x,y,z]; 
phi = x^3+y^3+z^3;
assert(dividedActionInDegree(2,phi)==matrix(ZZ/5,{{1,0,0,0,0,0},{0,0,0,1,0,0},{0,0,0,0,0,1}}))
assert(dividedKerInDegree(2, phi)==ideal(x*y,x*z,y*z))
assert(dividedImInDegree(2, phi)==ideal(x,y,z))

R=ZZ/5[x,y,z];
I=ideal(x^3+y^3+z^3,x*y^2+y*z^2+z*x^2);
assert(dividedActionInDegree(2,I_*)==matrix(ZZ/5,{{1,0,0,0,0,0},{0,0,0,1,0,0},{0,0,0,0,0,1},{0,0,1,1,0,0},{0,1,0,0,0,1},{1,0,0,0,1,0}}))
assert(dividedKerInDegree(2,I_*)==ideal(0_R))
assert(dividedImInDegree(2,I_*)=={ideal(x,y,z),ideal(x,y,z)})

///
