needsPackage "InverseSystems"
needsPackage "MCMApproximations"

isLevel = method()

isLevel Ideal := Boolean => I -> (
    R := ring I;
    if not isStandardGradedPolynomialRing R then (error "Expected an ideal in a standard graded polynomial ring.");
    if not isHomogeneous I then (error "Expected a homogeneous ideal.");
    p := pdim comodule I;
    if p =!= codim I then return false
    else (
	if rank (res I)_p == last flatten entries (coefficients numerator hilbertSeries(I, Reduce => true))_1 then true
	else false
	)
    ) 

isLevel QuotientRing := Boolean => A -> (
    R := ambient A;
    if not isStandardGradedPolynomialRing R then (error "Expected a quotient ring of a standard graded polynomial ring.");
    isLevel ideal A
    )


isCompressed = method()

isCompressed Ideal := Boolean => I -> (
    R := ring I;
    if not isStandardGradedPolynomialRing R then (error "Expected an ideal in a standard graded polynomial ring.");
    if not isHomogeneous I then (error "Expected a homogeneous ideal.");
    if dim I =!= 0 then (error "Expected an ideal with zero-dimensional quotient.");
    if not isLevel I then return false
    else (
	d := numgens R;
	c := first socleDegrees comodule I;
	s := rank source super basis(c, R/I);
	if all(c+1, 
	    i -> rank source super basis(i, R/I) == min(binomial(d+i-1,i), binomial(d+c-i-1,c-i)*s)
	    )to
	then true
	else false
	)
    )

isCompressed QuotientRing := Boolean => A -> (
    R := ambient A;
    if not isStandardGradedPolynomialRing R then (error "Expected a quotient ring of a standard graded polynoial ring.");
    isCompressed ideal A
    )
    

	
TEST ///
R = QQ[x,y,z]
I1 = ideal(x^2,y^2,z^2)
I2 = ideal(x^2,x*y,y^3)
I3 = ideal(x^2,y^2)
assert(isLevel I1 == true)
assert(isLevel I2 == false)
assert(isLevel I3 == true)
///    


TEST ///
R = ZZ/5[x,y]
I1 = ideal(x*y, x^3-y^3)
I2 = ideal(x^2*y-x*y^2, x^3+y^3-3*x^2*y)
R' = ZZ/5[x,y,z]
I3 = ideal(x^25,y^25,z^25,x*y^2+y*z^2+z*x^2)
assert(isCompressed I1 == true)
assert(isCompressed I2 == true)
assert(isCompressed I3 == false)
///    
