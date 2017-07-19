needsPackage "InverseSystems"

lowerExponent = method()

lowerExponent (RingElement, List) := RingElement => (phi,l) -> (
    D := ring phi;
    if not isStandardGradedPolynomialRing D then (error "Expected a polynomial in a standard graded polynomial ring.");
    if not #l == numgens D then (error "Expected the length of the list to be equal to the number of variables.");
    expList := exponents(phi);
    expList = select(expList, e->all(e-l,i->(i>=0)));
    sum(apply(expList,e->coefficient(D_e,phi)*D_(e-l)))
    )

lowerExponent (RingElement, RingElement) := RingElement => (phi, f) -> (
    D := ring phi;
    S := ring f;
    if not isStandardGradedPolynomialRing S then (error "Expected a polynomial in a standard graded polynomial ring.");
    if not numgens D == numgens S then (error "Expected the rings of the polynomials to have the same number of variables.") 
    exps := exponents(f);
    coeffs := (coefficients f)_1;
    ((matrix {apply(exps, l -> lowerExponent(phi, l))})*coeffs)_0_0
    )
    
    
    --newExponents := apply(oldExponents,e->(e-l));
    --newExponents = select(newExponents,e->all(e,i->(i>=0)));
    --R := ring(f);
    --apply(newExponents,e->R_(newExponents#e))
    
    
    --for i from 0 to length(oldExponents) 
    --newExponents = exponents(m)-l;
    --R=ring(m);
    --for i from 0 to length(newExponents) list(R_(newExponents_i))
    --for i from 0 to length(newExponents) list(
	--if newExponents#i < 0 then 0
      	--)
    
    