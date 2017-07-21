needsPackage "InverseSystems"

isLevel = method()

isLevel Ideal := I -> (
    A := ring I;
    if not isStandardGradedPolynomialRing A then (error "Expected an ideal in a standard graded polynomial ring.");
    p := pdim comodule I;
    if p =!= codim I then return false
    else (
	if rank (res I)_p == last flatten entries (coefficients numerator hilbertSeries(I, Reduce => true))_1 then true
	else false
	)
    ) 

isLevel QuotientRing := R -> (
    A := ambient R;
    if not isStandardGradedPolynomialRing A then (error "Expected a quotient ring of a standard graded polynomial ring.");
    isLevel ideal R
    )


	
TEST ///
A = QQ[x,y,z]
I1 = ideal(x^2,y^2,z^2)
I2 = ideal(x^2,x*y,y^3)
I3 = ideal(x^2,y^2)
assert(isLevel I1 == true)
assert(isLevel I2 == false)
assert(isLevel I3 == true)
///    
    
    
    R := ring I;
    if not isStandardGradedPolynomialRing R then (error "Expected an ideal in a standard graded polynomial ring.");
    