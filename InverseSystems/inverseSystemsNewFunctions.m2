--input: polynomial
--output: polynomial but in negative powers of variables
toNegativePowers = p -> (
    )

--input: polynomial in negative powers of variables
--output: polynomial in positive powers of variables
toPositivePowers = p -> (
    
    )

lowerExponent = method()

lowerExponent (RingElement, List) := RingElement => (phi,l) -> ( --input: polynomial, list of positive powers
    --output: new monomial in negative powers lowered by positive amounts
    expList := exponents(phi);
    expList = select(expList, e->all(e-l,i->(i>=0)));
    sum(apply(expList,e->coefficient(R_e,phi)*R_(e-l)))
    )

lowerExponent (RingElement, RingElement) := RingElement => (phi, f) -> (
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
    
    