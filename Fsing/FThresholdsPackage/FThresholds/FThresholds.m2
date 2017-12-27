--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------------------------
-- CONTENTS
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

----------------------------------------------------------------------------------
-- Nu computations

-- Main functions: nuList, nu

-- Auxiliary Functions: nu1, binarySearch, binarySearchRecursive, linearSearch,
--     testPower, testRoot, testFrobeniusPower, nuInternal

----------------------------------------------------------------------------------
-- FThreshold Approximations

-- Main functions: FPTApproxList, FTApproxList, FTHatApproxList

----------------------------------------------------------------------------------
-- FThreshold Estimates

-- Main functions: guessFPT, estFPT

----------------------------------------------------------------------------------
-- FPT/F-Jumping number check

-- Main functions: isFPTPoly, isFJumpingNumberPoly


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------------------------
-- Functions for computing \(nu_I)^J(p^e), \(nu_f)^J(p^e)
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


----------------------------------------------------------------------------------
-- nu1(I,J) finds the maximal N such that I^N is not contained in J, i.e., nu_I^J(1)
nu1 = method()

nu1 ( Ideal, Ideal ) :=  ( I, J ) -> 
(
    if not isSubset( I, radical J ) then 
        error "nu1: The first ideal is not contained in the radical of the second.";
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

-- for polynomials, we use fastExponentiation
nu1 ( RingElement, Ideal ) := ( f, J ) -> 
(
    if not isSubset( ideal f, radical J ) then 
        error "nu1: The polynomial is not contained in the radical of the ideal.";
    d := 1;
    while not isSubset( ideal fastExponentiation( d, f ), J ) do d = d + 1;
    d - 1
)

----------------------------------------------------------------------------------
-- TESTS

-- testRoot(J,a,I,e) checks whether J^a is a subset of I^[p^e], using frobeniusRoot
testRoot = ( J, a, I, e ) -> isSubset( frobeniusRoot( e, a, J ), I )

-- testPower(J,a,I,e) checks whether J^a is  a subset of I^[p^e], directly
testPower = method()

testPower ( Ideal, ZZ, Ideal, ZZ ) := ( J, a, I, e ) -> 
    isSubset( J^a, frobenius( e, I ) )

-- for polynomials, use fastExponentiation
testPower ( RingElement, ZZ, Ideal, ZZ ) := ( f, a, I, e ) -> 
    isSubset( ideal fastExponentiation( a, f ), frobenius( e, I ) )

-- testFrobeniusPower(J,a,I,e) checks whether J^[a] is a subset of I^[p^e]
testFrobeniusPower = ( J, a, I, e ) -> 
    isSubset( frobeniusPower( a, J ), frobenius( e, I ) )

----------------------------------------------------------------------------------
-- SEARCH FUNCTIONS

-- Each *Search(I,J,e,a,b,test) searches for the last n in [a,b) such that test(I,n,J,e) 
-- is false, assuming that test(I,a,J,e) is false and test(I,b,J,e) is true.

-- Non-recursive binary search, based on our previous code
binarySearch = ( I, J, e, startPt, endPt, testFunction ) -> 
(
    a := startPt;
    b := endPt; 
    local c;   
    while b > a+1 do 
    (
	c = floor( (a+b)/2 );
	if testFunction( I, c, J, e ) then b = c else a = c
    );
    a
)

-- Recursive binary search
binarySearchRecursive = ( I, J, e, a, b, testFunction ) -> 
(
    if b <= a+1 then return a;
    c := floor( (a+b)/2 );
    if testFunction( I, c, J, e ) 
        then binarySearchRecursive( I, J, e, a, c, testFunction ) 
	else binarySearchRecursive( I, J, e, c, b, testFunction )
)

-- Linear search
linearSearch = ( I, J, e, a, b, testFunction ) -> 
(
    c := a + 1;
    while not testFunction( I, c, J, e ) do c = c+1;
    c-1
)

----------------------------------------------------------------------------------
-- OPTION PACKAGES

optIL = { TestFunction => testPower, UseColonIdeals => false, SearchFunction => binarySearch }

optPL = { TestFunction => testRoot, UseColonIdeals => false, SearchFunction => binarySearch }

optI = append( optIL, ComputePreviousNus => true )

optP = append( optPL, ComputePreviousNus => true )

----------------------------------------------------------------------------------
-- INTERNAL FUNCTION

nuInternal = optI >> o -> ( n, f, J ) -> 
( 
    p := char ring f;
    nu := nu1( f, J );
    theList := { nu };
    principal := if isIdeal f then (numgens trim f) == 1 else true;
    local N;
    if not o.ComputePreviousNus then
    (
	if n == 0 then return theList;
 	N = if principal or o.TestFunction === testFrobeniusPower
	     then p^n else (numgens trim J)*(p^n-1)+1;
     	return { o.SearchFunction( f, J, n, nu*p^n, (nu+1)*N, o.TestFunction ) }
    );
    if o.UseColonIdeals and principal then -- colon ideals only work for polynomials
    (
	I := J;
	g := if isIdeal f then (trim f)_*_0 else f; 
	scan( 1..n, e ->
	    (
		I = I : ideal( fastExponentiation( nu, g ) );
		nu =  last nuInternal( 1, g, I, TestFunction => o.TestFunction );
	      	theList = append( theList, p*(last theList) + nu );
	      	I = frobenius( I )
	    )
	)
    )
    else
    (
	N = if principal or o.TestFunction === testFrobeniusPower
	     then p else (numgens trim J)*(p-1)+1;
	scan( 1..n, e -> 
	    (
		nu = o.SearchFunction( f, J, e, p*nu, (nu+1)*N, o.TestFunction );
    	       	theList = append( theList, nu )
    	    )
    	)
     );
     theList
)

----------------------------------------------------------------------------------
-- EXPORTED METHODS

nuList = method( Options => true )

nuList( ZZ, Ideal, Ideal ) := optIL >> o -> ( e, I, J ) -> nuInternal( e, I, J, o )

nuList( ZZ, RingElement, Ideal ) := optPL >> o -> ( e, I, J ) -> nuInternal( e, I, J, o )

nuList( ZZ, Ideal ) := optIL >> o -> ( e, I ) -> nuList( e, I, maxIdeal I, o )

nuList( ZZ, RingElement ) := optPL >> o -> ( e, f ) -> nuList( e, f, maxIdeal f, o )

nu = method( Options => true )

nu( ZZ, Ideal, Ideal ) := optI >> o -> ( e, I, J ) -> last nuInternal( e, I, J, o )

nu( ZZ, RingElement, Ideal ) := optP >> o -> ( e, f, J ) -> last nuInternal( e, f, J, o )

nu( ZZ, Ideal ) := optI >> o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu( ZZ, RingElement ) := optP >> o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

-- Nus can be computed using generalized Frobenius powers, by using 
-- TestFunction=>testFrobeniusPower. For convenience, here are some shortcuts: 

muList = optIL >> o -> x -> nuList( x, o, TestFunction => testFrobeniusPower ) 

mu = optI >> o -> x -> nu( x, o, TestFunction => testFrobeniusPower ) 

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------------------------
-- Functions for approximating, guessing, estimating F-Thresholds and critical Exp
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Approximates the F-pure Threshold
--Gives a list of nu_I(p^d)/p^d for d=1,...,e
FPTApproxList = method();

FPTApproxList ( ZZ, Ideal ) := (e, I) ->
(
     p := char ring I;
     nus := nuList(e,I);
     apply( nus, 1..e, (n,k) -> n/p^k )
)

FPTApproxList ( ZZ, RingElement ) := ( e, f ) -> FPTApproxList( e, ideal(f) )

--Approximates the F-Threshold with respect to an ideal J
--More specifically, this gives a list of nu_I^J(p^d)/p^d for d=1,...,e

FTApproxList = method();

FTApproxList ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical(J) ) then error "F-threshold undefined.";
     p := char ring I;
     nus := nuList(e,I,J);
     apply( nus, 1..e, (n,k) -> n/p^k )
)

FTApproxList ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> FTApproxList( e, ideal(f), J )

critExpApproxList = method();

critExpApproxList ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical(J) ) then error "critExpApproxList: critical exponent undefined.";
     p := char ring I;
     mus := muList( e, I, J );
     apply( mus, 1..e, (n,k) -> n/p^k )
)

critExpApproxList ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> critExpApproxList( e, ideal(f), J )

--Guesses the FPT of ff.  It returns a list of all numbers in 
--the range suggested by nu(e1,ff) with maxDenom as the maximum denominator
guessFPT ={OutputRange=>false}>>o -> (ff, e1, maxDenom) ->(
     nn := nu(e1,ff);
     pp := char ring ff;
     if (o.OutputRange == false) then 
          findNumberBetween( maxDenom, nn/(pp^e1-1), (nn+1)/(pp^e1) )
     else
          { {nn/(pp^e1-1), (nn+1)/(pp^e1)}, findNumberBetween( maxDenom, nn/(pp^e1-1), (nn+1)/(pp^e1) ) }
)

----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------
 
--- Computes the F-signature for a specific value a1/p^e1
--- Input:
---	e - some positive integer
---	a - some positive integer between 0 and p^e
---	f - some polynomial in two or three variables in a ring R of PRIME characteristic
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Code is based on work of Eric Canton
fSig = (f, a, e) -> (
     R := ring f;
     p := char ring f;     
     1 - p^(-e*dim(R))*degree( frobenius( e, maxIdeal R) + ideal( fastExponentiation( a, f ) )) 
)  

--Calculates the x-int of the secant line between two guesses for the fpt
--Input:
--     t - some positive rational number
--     b - the f-signature of (R,f^{t/p^e})
--     e - some positive integer
--     t1- another rational number > t
--     f - some polynomial in two or three variables in a ring of PRIME characteristic
--
-- Output:
--	fSig applied to (f,t1,e)
--	x-intercept of the line passing through (t,b) and (t1,fSig(f,t1,e))
threshInt = (f,e,t,b,t1)-> (
     b1:=fSig(f,t1,e);
{b1,xInt(t,b,t1/(char ring f)^e,b1)}
)

isFRegularPoly = method();

--Determines if a pair (R, f^t) is F-regular at a prime
--ideal Q in R, R is a polynomial ring  
isFRegularPoly (RingElement, QQ, Ideal) := (f1, t1, Q1) -> (
     not isSubset(testIdeal(t1,f1), Q1)
)

--Determines if a pair (R, f^t) is F-regular, R a polynomial ring
isFRegularPoly (RingElement, QQ) := (f1, t1) -> (
     isSubset(ideal(1_(ring f1)), testIdeal(t1,f1))
)


--F-pure threshold estimation, at the origin
--e is the max depth to search in
--FinalCheck is whether the last isFRegularPoly is run (it is possibly very slow) 
--If MultiThread is set to true, it will compute the two F-signatures simultaneously
estFPT={FinalCheck=> true, Verbose=> false, MultiThread=>false, DiagonalCheck=>true, BinomialCheck=>true, NuCheck=>true} >> o -> (ff,ee)->(
     print "starting estFPT";
     
     maxIdeal := ideal( first entries vars( ring ff) );   --the maximal ideal we are computing the fpt at  

     foundAnswer := false; --this will be set to true as soon as we found the answer.  Setting it to true will stop further tests from being run
     answer := null; --this stores the answer until it can be returned.
     
     --first check if it is diagonal:
     if ( (o.DiagonalCheck==true) and (foundAnswer == false) ) then (
	   if (isDiagonal(ff)==true) then ( 
		if (o.Verbose==true) then print "Polynomial is diagonal."; 
		answer = diagonalFPT(ff); 
		foundAnswer = true
	   )
     );

     --now check if it is binomial:
     if ( (o.BinomialCheck==true) and (foundAnswer == false) ) then (
	  if (isBinomial(ff)==true) then ( 
	       if  (o.Verbose==true) then print "Polynomial is binomial.";
	       answer = binomialFPT(ff);
	       foundAnswer = true
	  )
     );
     
     --compute nu's
     if (foundAnswer == false) then (
     	  pp:=char ring ff;
     	  nn:=nu(ee,ff);
	  if  (o.Verbose==true) then print "nu's have been computed";

     	  --if our nu's aren't fine enough, we just spit back some information
       	  if nn==0 then (
	       answer = {0,1/pp};
	       foundAnswer = true
	   )
      );
 
      --check to see if nu/(p^e-1) is the fpt
      if ((o.NuCheck==true) and (foundAnswer == false)) then (
	   if (isFRegularPoly(ff,(nn/(pp^ee-1)),maxIdeal)==false) then ( 
		if  (o.Verbose==true) then print "Found answer via nu/(p^e-1)."; 
		answer = nn/(pp^ee-1);
		foundAnswer = true
	   ) 
      	   else (
	   	if  (o.Verbose==true) then print "nu/(p^e - 1) is not the fpt.";
	   )
      );
	 
	--check to see if (nu+1)/p^e is the FPT
	if ((o.NuCheck==true) and (foundAnswer == false)) then(
		if (isFPTPoly(ff, (nn+1)/pp^ee,Origin=>true) == true) then (
			answer = (nn+1)/pp^ee;
			foundAnswer = true
		)
	);

     --do the F-signature computation
     if (foundAnswer == false) then (
	   ak := 0;
	   if (o.MultiThread==false ) then (ak=threshInt(ff,ee,(nn-1)/pp^ee,fSig(ff,nn-1,ee),nn) ) else(
		if (o.Verbose==true) then print "Beginning multithreaded F-signature";
		allowableThreads = 4;
		numVars := rank source vars (ring ff);
		YY := local YY;
		myMon := monoid[  toList(YY_1..YY_numVars), MonomialOrder=>RevLex,Global=>false];
		--print myMon;
     		R1:=(coefficientRing ring ff) myMon;
		rMap := map(R1, ring ff, vars myMon);
		gg := rMap(ff);
		
		
		H := (fff,aaa,eee) -> () -> fSig(fff,aaa,eee);
		newSig1 := H(gg,nn-1,ee);
		t1 := schedule newSig1;
	     	s2 := fSig(ff,nn,ee);	
		if (o.Verbose==true) then print "One signature down";
		while ((not isReady t1)) do sleep 1;
		s1 := taskResult t1;
     	      --  print s1; print s2;
		ak = {s2,xInt( (nn-1)/pp^ee, s1, (nn)/pp^ee,s2)};
		--print nn;		
	   );
	   if  (o.Verbose==true) then print "Computed F-signatures.";
	   --now check to see if we cross at (nu+1)/p^e, if that's the case, then that's the fpt.
	   if ( (nn+1)/pp^ee == (ak#1) ) then (
		if  (o.Verbose==true) then print "F-signature line crosses at (nu+1)/p^e."; 
		answer = ak#1;
		foundAnswer = true
	   )
      );	  
      	
      --if we run the final check, do the following
      if ( (foundAnswer == false) and (o.FinalCheck == true)) then ( 
	  if  (o.Verbose==true) then print "Starting FinalCheck."; 
          	if ((isFRegularPoly(ff,ak#1,maxIdeal)) ==false ) then (	
	      		if  (o.Verbose==true) then print "FinalCheck successful"; 
	      		answer = (ak#1);
	      		foundAnswer = true 
      	  	)
	  		else ( 
	      		if  (o.Verbose==true) then print "FinalCheck didn't find the fpt."; 
	      		answer = {(ak#1),(nn+1)/pp^ee};
	      		foundAnswer = true
	  		)
       );
       
       --if we don't run the final check, do the following
       if ((foundAnswer == false) and (o.FinalCheck == false) ) then (
	  if  (o.Verbose==true) then print "FinalCheck not run.";
	  answer = {(ak#1),(nn+1)/pp^ee};
      	  foundAnswer = true
       );
     
     --return the answer
     answer
)

-- essentially same as estFPT, with small additions and changes to make the code clearer
fpt = method( 
    TypicalValue => QQ, 
    Options => 
        {
	    FinalCheck => true, 
	    Verbose => false, 
	    MultiThread => false, 
	    DiagonalCheck => true, 
	    BinomialCheck => true, 
	    BinaryFormCheck => true, 
	    NuCheck => true 
    	}
);

fpt ( RingElement, ZZ ) := QQ => o -> ( f, e ) -> 
(
    -- To do: check if f is a polynomial over a field of positive char

    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at  
    p := char ring f;
    if not isSubset( ideal f, M ) then error "Polynomial is not in the homogeneous maximal ideal";   

    if o.Verbose then print "Starting fpt";
    
    -- Check if fpt equals 1
    if not isSubset( ideal( f^(p-1) ), frobenius( M ) ) then 
    (
        if o.Verbose then print "nu(1,f) = p-1, so fpt(f) = 1"; 
        return 1 
    );	
    
    if o.Verbose then print "fpt(f) is not 1";
    
    -- Check if one of the special FPT functions can be used...
    
    -- Check if it is diagonal:
    if o.DiagonalCheck and isDiagonal f then 
    ( 
        if o.Verbose then print "Polynomial is diagonal"; 
        return diagonalFPT f 
    );

    -- Now check if it is binomial:
    if o.BinomialCheck and isBinomial f then 
    ( 
        if o.Verbose then print "Polynomial is a binomial";
        return binomialFPT f 
    );

    -- Now check if it is a binary form:
    if o.BinaryFormCheck and isBinaryForm f then 
    ( 
        if o.Verbose then print "Polynomial is a binary form";
        return binaryFormFPT f 
    );
    
    if o.Verbose then print "Special fpt algorithms are not available for this polynomial";
     
    -- Compute nu(e,f)
    n := nu( e, f );
        
    if o.Verbose then print( "nu has been computed: nu(e,f) = " | toString n );
    
    -- If our nu isn't fine enough, we just spit back some information
    if n == 0 then 
    (
	if o.Verbose then 
	    print "The nu computed isn't fine enough. Try increasing the max exponent e.";
	return { 0, 1/p^e }
    );

    -- Check to see if either nu/(p^e-1) or (nu+1)/p^e is the fpt
    if o.NuCheck then 
    (
        --check to see if nu/(p^e-1) is the fpt
	if not isFRegularPoly( f, n/( p^e - 1 ), M ) then 
	(
	    if o.Verbose then print "Found answer via nu/(p^e-1)"; 
	    return n/( p^e - 1 )
	) 
      	else if o.Verbose then print "nu/(p^e-1) is not the fpt";
	
        --check to see if (nu+1)/p^e is the FPT
	if isFPTPoly( ( n + 1 )/p^e, f ) then 
	(
	    if o.Verbose then print "Found answer via (nu+1)/(p^e)"; 
	    return ( n + 1 )/p^e
	) 
      	else if o.Verbose then print "(nu+1)/p^e is not the fpt"
    );

    -- Do the F-signature computation
    a := 0;
    if  not o.MultiThread then a = threshInt( f, e, (n-1)/p^e, fSig( f, n-1 , e ), n ) 
    else
    (
	if o.Verbose then print "Beginning multithreaded F-signature";
	allowableThreads = 4;
	numVars := #(ring f)_*;
	Y := local Y;
	myMon := monoid[ toList(Y_1..Y_numVars), MonomialOrder => RevLex, Global => false ];
	R := (coefficientRing ring f) myMon;
	rMap := map( R, ring f, vars myMon);
	g := rMap f;
	t := schedule( fSig, ( g, n-1, e ) );
	s2 := fSig( f, n, e );	
	if o.Verbose then print("First F-signature: s(f,nu/p^e) = " | toString s2);
	while not isReady t do sleep 1;
	s1 := taskResult t;
	if o.Verbose then print("Second F-signature: s(f,(nu-1)/p^e) = " | toString s1);
	a = { s2, xInt( (n-1)/p^e, s1, n/p^e, s2 )}
    );
    if o.Verbose then print( "Computed F-signature intercept: " | toString a#1);

    -- Now check to see if we cross at (nu+1)/p^e. If so, then that's the fpt.
    if (n+1)/p^e == a#1 then 
    (
	if  o.Verbose then print "F-signature line crosses at (nu+1)/p^e"; 
	return a#1
    );
	       	
    if o.FinalCheck then 
    (
	if o.Verbose then print "Starting FinalCheck"; 
 --       if not isFRegularPoly( f, a#1, M ) then 
 -- trying isFPT here
        if isFPTPoly( a#1, f ) then 
        (	
	   if o.Verbose then print "FinalCheck successful"; 
	   return a#1
      	)
	else if o.Verbose then print "FinalCheck didn't find the fpt"
    )
    else if o.Verbose then print "FinalCheck not run";    
    { a#1, (n+1)/p^e }
)

-- a different version, where multithread is done without cloning the ring and poly
-- essentially same as estFPT, with small additions and changes to make the code clearer
fpt1 = method( 
    TypicalValue => QQ, 
    Options => 
        {
	    FinalCheck => true, 
	    Verbose => false, 
	    MultiThread => false, 
	    DiagonalCheck => true, 
	    BinomialCheck => true, 
	    BinaryFormCheck => true, 
	    NuCheck => true 
    	}
);

fpt1 ( RingElement, ZZ ) := QQ => o -> ( f, e ) -> 
(
    -- To do: check if f is a polynomial over a field of positive char

    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at  
    p := char ring f;
    if not isSubset( ideal f, M ) then error "Polynomial is not in the homogeneous maximal ideal";   

    if o.Verbose then print "Starting fpt";
    
    -- Check if fpt equals 1
    if not isSubset( ideal( f^(p-1) ), frobenius( M ) ) then 
    (
        if o.Verbose then print "nu(1,f) = p-1, so fpt(f) = 1"; 
        return 1 
    );	
    
    if o.Verbose then print "fpt(f) is not 1";
    
    -- Check if one of the special FPT functions can be used...
    
    -- Check if it is diagonal:
    if o.DiagonalCheck and isDiagonal f then 
    ( 
        if o.Verbose then print "Polynomial is diagonal"; 
        return diagonalFPT f 
    );

    -- Now check if it is binomial:
    if o.BinomialCheck and isBinomial f then 
    ( 
        if o.Verbose then print "Polynomial is a binomial";
        return binomialFPT f 
    );

    -- Now check if it is a binary form:
    if o.BinaryFormCheck and isBinaryForm f then 
    ( 
        if o.Verbose then print "Polynomial is a binary form";
        return binaryFormFPT f 
    );
    
    if o.Verbose then print "Special fpt algorithms are not available for this polynomial";
     
    -- Compute nu(e,f)
    n := nu( e, f ); 
    
    if o.Verbose then print( "nu has been computed: nu(e,f) = " | toString n );
    
    -- If our nu isn't fine enough, we just spit back some information
    if n == 0 then 
    (
	if o.Verbose then 
	    print "The nu computed isn't fine enough. Try increasing the max exponent e.";
	return { 0, 1/p^e }
    );

    -- Check to see if either nu/(p^e-1) or (nu+1)/p^e is the fpt
    if o.NuCheck then 
    (
        --check to see if nu/(p^e-1) is the fpt
	if not isFRegularPoly( f, n/( p^e - 1 ), M ) then 
	(
	    if o.Verbose then print "Found answer via nu/(p^e-1)"; 
	    return n/( p^e - 1 )
	) 
      	else if o.Verbose then print "nu/(p^e-1) is not the fpt";
	
        --check to see if (nu+1)/p^e is the FPT
	if isFPTPoly( ( n + 1 )/p^e, f ) then 
	(
	    if o.Verbose then print "Found answer via (nu+1)/(p^e)"; 
	    return ( n + 1 )/p^e
	) 
      	else if o.Verbose then print "(nu+1)/p^e is not the fpt"
    );

    -- Do the F-signature computation
    a := 0;
    if  not o.MultiThread then a = threshInt( f, e, (n-1)/p^e, fSig( f, n-1 , e ), n ) 
    else
    (
	if o.Verbose then print "Beginning multithreaded F-signature";
	t := schedule( fSig, ( f, n-1, e ) );
	s2 := fSig( f, n, e );	
	if o.Verbose then print("First F-signature: s(f,nu/p^e) = " | toString s2);
	while not isReady t do sleep 1;
	s1 := taskResult t;
	if o.Verbose then print("Second F-signature: s(f,(nu-1)/p^e) = " | toString s1);
	a = { s2, xInt( (n-1)/p^e, s1, n/p^e, s2 )}
    );
    if o.Verbose then print( "Computed F-signature intercept: " | toString a#1);

    -- Now check to see if we cross at (nu+1)/p^e. If so, then that's the fpt.
    if (n+1)/p^e == a#1 then 
    (
	if  o.Verbose then print "F-signature line crosses at (nu+1)/p^e"; 
	return a#1
    );
	       	
    if o.FinalCheck then 
    (
	if o.Verbose then print "Starting FinalCheck"; 
 --       if not isFRegularPoly( f, a#1, M ) then 
 -- trying isFPT here
        if isFPTPoly( a#1, f ) then 
        (	
	   if o.Verbose then print "FinalCheck successful"; 
	   return a#1
      	)
	else if o.Verbose then print "FinalCheck didn't find the fpt"
    )
    else if o.Verbose then print "FinalCheck not run";    
    { a#1, (n+1)/p^e }
)



--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------------------------
-- Functions for checking if given numbers are F-jumping numbers
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--isFPTPoly, determines if a given rational number is the FPT of a pair in a polynomial ring. 
--if Origin is specified, it only checks at the origin. 

isFPTPoly = method( Options => {Verbose=> false,Origin=>false} )
isFPTPoly ( QQ, RingElement ) := o -> ( t, f ) -> 
(
	p := char ring f;
	if (o.Origin == true) then org := ideal(vars (ring f));
	--this writes t = a/(p^b(p^c-1))
	(a,b,c) := toSequence decomposeFraction( p, t );
	mySigma := ideal(f);
	myTau := ideal(sub(1, ring f));
	myA := a;
	myA2 := 0;
	
	if (c != 0) then (
		myA = floor(a / (p^c - 1));
		myTau = testIdeal( (a%(p^c-1))/(p^c-1), f )
	);
	
	if (o.Verbose==true) then print "higher tau Computed";

	--first we check whether this is even a jumping number.
	if (c == 0) then (
		myA2 = a-1;
		mySigma = sigmaAOverPEMinus1Poly(f, (p-1), 1)
	)
	else (
		myA2 = floor((a-1)/(p^c-1));
		mySigma = (sigmaAOverPEMinus1Poly(f, ((a-1)%(p^c-1))+1, c))
	);
	if (o.Verbose==true) then print "higher sigma Computed";

	returnValue := false;
	
	if ( isSubset(ideal(sub(1, ring f)), frobeniusRoot(b, myA2, f , mySigma ) )) then (
		if (o.Verbose==true) then print "we know t <= FPT";
		if (not isSubset(ideal(sub(1, ring f)), frobeniusRoot( b, myA, f, myTau ) ))  then returnValue = true 
	);
		
	returnValue
)

--isFJumpingNumberPoly determines if a given rational number is an F-jumping number
--***************************************************************************
--This needs to be speeded up, like the above function
--***************************************************************************

isFJumpingNumberPoly = method( Options => {Verbose=> false} )

isFJumpingNumberPoly ( QQ, RingElement ) := o -> ( t, f ) -> 
(
	p := char ring f;
	--this writes t = a/(p^b(p^c-1))
	(a,b,c) := toSequence decomposeFraction( p, t );
	mySigma := ideal(f);
	myTau := frobeniusRoot(b, testIdeal(t*p^b, f) );
	if (o.Verbose==true) then print "higher tau Computed";

	--first we check whether this is even a jumping number.
	if (c == 0) then
		mySigma = frobeniusRoot(b,(ideal(f^(a-1)))*((sigmaAOverPEMinus1Poly(f, (p-1), 1))))
	else 
		mySigma = frobeniusRoot(b,(sigmaAOverPEMinus1Poly(f, a, c)));
	if (o.Verbose==true) then print "sigma Computed";

	not (isSubset(mySigma, myTau))
)

----------------------------------------------------------------
--************************************************************--
--Functions for computing sigma                               --
--************************************************************--
----------------------------------------------------------------


--Computes Non-Sharply-F-Pure ideals over polynomial rings for (R, fm^{a/(p^{e1}-1)}), 
--at least defined as in Fujino-Schwede-Takagi.
sigmaAOverPEMinus1Poly ={HSL=> false}>> o -> (fm, a1, e1) -> ( 
     Rm := ring fm;
     pp := char Rm;
     m1 := 0;
	e2 := e1;
	a2 := a1;
	--if e1 = 0, we treat (p^e-1) as 1.  
     if (e2 == 0) then (e2 = 1; a2 = a1*(pp-1));
     if (a2 > pp^e2-1) then (m1 = floor((a2-1)/(pp^e2-1)); a2=((a2-1)%(pp^e2-1)) + 1 );
     --fpow := fm^a2;
     IN := frobeniusRoot(e2,ideal(1_Rm)); -- this is going to be the new value.
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  This stops after finitely many steps.  
     while (IN != IP) do(
		IP = IN;
	  	IN = frobeniusRoot(e2,a2,fm,IP); -- ethRoot(e2,ideal(fpow)*IP);
	  	count = count + 1
     );

     --return the final ideal and the HSL number of this function
     if (o.HSL == true) then {IP*ideal(fm^m1),count} else IP*ideal(fm^m1)
)
