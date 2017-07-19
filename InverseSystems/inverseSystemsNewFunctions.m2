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
    if i > d or i < 0 then (error "Expected a non-negative integer no bigger than the degree of the polynomial.");
    matrix apply(flatten entries super basis(d - i, D), 
	m -> apply(flatten entries super basis(i, D),
	    u -> coefficient(m, lowerExponent(phi, u))
	    )
	)
    )

--Input: A homogeneous polynomial 'phi' representing an element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The matrix representing multiplication by 'phi' on the degree 'i' component of the dual polynomial ring.


-----------------------------------------------------------
    
dividedKerInDegree = method()    
    
dividedKerInDegree (ZZ, RingElement) := Ideal => (i, phi) -> (
    if not isHomogeneous phi then (error "Expected a homogeneous polynomial.");
    K := gens ker dividedActionInDegree(i, phi);
    D := ring phi;
    prune ideal( (super basis(i, D)) * K )
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
    prune ideal( (super basis(i, D) * A) )
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
    if not isHomogeneous phi then (error "Expected a homogeneous polynomial.");
    I := gens image dividedActionInDegree(i, phi);
    D := ring phi;
    d := (degree phi)#0;
    prune ideal( (super basis(d-i, D)) * I )
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
    prune ideal( (super basis(d - i, D) * A) )
    )

--Input: A matrix 'A' representing multiplication by a homogeneous element of a divided powers algebra and an non-negative integer 'i' no bigger than the degree of 'phi'.
--Output: The image of multiplication by 'A' in the dual polynomial ring.


TEST ///

S = ZZ/7[x,y,z] 
phi = x^5*y^4*z^6 + x^6*y^5*z^4+x^4*y^6*z^5
dividedKerInDegree(7, phi)
dividedImInDegree(8, phi)

///
