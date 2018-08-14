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

-- Main functions: fptApproximation, ftApproximation, criticalExponentApproximation

----------------------------------------------------------------------------------
-- FThreshold Estimates

-- Main functions: guessFPT, estFPT

----------------------------------------------------------------------------------
-- FPT/F-Jumping number check

-- Main functions: isFPT, isFJumpingNumber


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------------------------
-- Functions for computing (nu_I)^J(p^e), (nu_f)^J(p^e)
----------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


----------------------------------------------------------------------------------
-- nu1(I,J) finds the maximal N such that I^N is not contained in J, i.e., nu_I^J(1)
nu1 = method()

nu1 ( Ideal, Ideal ) :=  ( I, J ) -> 
(
    if not isSubset( I, radical J ) then 
        error "nu1: The first ideal is not contained in the radical of the second";
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

-- for polynomials, we use fastExponentiation
nu1 ( RingElement, Ideal ) := ( f, J ) -> 
(
    if not isSubset( ideal f, radical J ) then 
        error "nu1: The polynomial is not contained in the radical of the ideal";
    d := 1;
    while not isSubset( ideal fastExponentiation( d, f ), J ) do d = d + 1;
    d - 1
)

----------------------------------------------------------------------------------
-- TESTS
-- purpose is to verify containment in Frobenius powers

-- testRoot(J,a,I,e) checks whether J^a is a subset of I^[p^e] by checking whether (J^a)^[1/p^e] is a subset of I
testRoot = ( J, a, I, e ) -> isSubset( frobeniusRoot( e, a, J ), I )

-- testPower(J,a,I,e) checks whether J^a is  a subset of I^[p^e], directly
testPower = method()

testPower ( Ideal, ZZ, Ideal, ZZ ) := ( J, a, I, e ) -> 
    isSubset( J^a, frobenius( e, I ) )

-- for polynomials, use fastExponentiation
testPower ( RingElement, ZZ, Ideal, ZZ ) := ( f, a, I, e ) -> 
    isSubset( ideal fastExponentiation( a, f ), frobenius( e, I ) )

-- testFrobeniusPower(J,a,I,e) checks whether J^[a] is a subset of I^[p^e]
testFrobeniusPower = method()

testFrobeniusPower ( Ideal, ZZ, Ideal, ZZ ) := ( J, a, I, e ) -> 
    isSubset( frobeniusPower( a, J ), frobenius( e, I ) )

testFrobeniusPower ( RingElement, ZZ, Ideal, ZZ ) := ( f, a, I, e ) -> testRoot( f, a, I, e )

-- hash table to select test function from option keyword
test := new HashTable from { FrobeniusPower => testFrobeniusPower, FrobeniusRoot => testRoot, StandardPower => testPower }

----------------------------------------------------------------------------------
-- SEARCH FUNCTIONS

-- Each *Search(I,J,e,a,b,testFunction) searches for the last n in [a,b) such that 
-- testFunction(I,n,J,e) is false, assuming that test(I,a,J,e) is false and test(I,b,J,e) 
-- is true.

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

-- hash table to select search function from option keyword
search = new HashTable from { Binary => binarySearch, BinaryRecursive => binarySearchRecursive, Linear => linearSearch }

----------------------------------------------------------------------------------
-- OPTION PACKAGES

optIdealList = { ContainmentTest => StandardPower, UseColonIdeals => false, Search => Binary }

optPolyList = { ContainmentTest => FrobeniusRoot, UseColonIdeals => false, Search => Binary }

optIdeal = append( optIdealList, ComputePreviousNus => true )

optPoly = append( optPolyList, ComputePreviousNus => true )

----------------------------------------------------------------------------------
-- INTERNAL FUNCTION

nuInternal = optIdeal >> o -> ( n, f, J ) -> 
(
    -- verify if option values are valid
    checkOptions( o,
	{
	    ContainmentTest => { StandardPower, FrobeniusRoot, FrobeniusPower },
	    Search => { Binary, Linear, BinaryRecursive },
	    UseColonIdeals => Boolean,
	    ComputePreviousNus => Boolean
	}
    );

    -- Check if polynomial has coefficients in a finite field
        if not isPolynomialOverFiniteField f  then 
        error "nu: expected polynomial with coefficients in a finite field";
 
    p := char ring f;
    nu := nu1( f, J );
    theList := { nu };
    isPrincipal := if isIdeal f then (numgens trim f) == 1 else true;
    local N;
    searchFct := search#(o.Search);
    testFct := test#(o.ContainmentTest);
    if not o.ComputePreviousNus then
    (
	if n == 0 then return theList;
 	N = if isPrincipal or o.ContainmentTest === FrobeniusPower
	     then p^n else (numgens trim J)*(p^n-1)+1;
     	return { searchFct( f, J, n, nu*p^n, (nu+1)*N, testFct ) }
    );
    if o.UseColonIdeals and isPrincipal then -- colon ideals only work for polynomials
    (
	I := J;
	g := if isIdeal f then (trim f)_*_0 else f; 
	scan( 1..n, e ->
	    (
		I = I : ideal( fastExponentiation( nu, g ) );
		nu =  last nuInternal( 1, g, I, ContainmentTest => o.ContainmentTest );
	      	theList = append( theList, p*(last theList) + nu );
	      	I = frobenius I
	    )
	)
    )
    else
    (
	N = if isPrincipal or o.ContainmentTest === FrobeniusPower
	     then p else (numgens trim J)*(p-1)+1;
	scan( 1..n, e -> 
	    (
		nu = searchFct( f, J, e, p*nu, (nu+1)*N, testFct );
    	       	theList = append( theList, nu )
    	    )
    	)
     );
     theList
)

----------------------------------------------------------------------------------
-- EXPORTED METHODS

nuList = method( Options => true )

nuList( ZZ, Ideal, Ideal ) := optIdealList >> o -> ( e, I, J ) -> 
    nuInternal( e, I, J, o )

nuList( ZZ, RingElement, Ideal ) := optPolyList >> o -> ( e, I, J ) -> 
    nuInternal( e, I, J, o )

nuList( ZZ, Ideal ) := optIdealList >> o -> ( e, I ) -> 
    nuList( e, I, maxIdeal I, o )

nuList( ZZ, RingElement ) := optPolyList >> o -> ( e, f ) -> 
    nuList( e, f, maxIdeal f, o )

nu = method( Options => true )

nu( ZZ, Ideal, Ideal ) := optIdeal >> o -> ( e, I, J ) -> 
    last nuInternal( e, I, J, o )

nu( ZZ, RingElement, Ideal ) := optPoly >> o -> ( e, f, J ) -> 
    last nuInternal( e, f, J, o )

nu( ZZ, Ideal ) := optIdeal >> o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu( ZZ, RingElement ) := optPoly >> o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

-- Nus can be computed using generalized Frobenius powers, by using 
-- ContainmentTest => FrobeniusPower. For convenience, here are some shortcuts: 

muList = optIdealList >> o -> x -> nuList( x, o, ContainmentTest => FrobeniusPower ) 

mu = optIdeal >> o -> x -> nu( x, o, ContainmentTest => FrobeniusPower ) 

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for approximating, guessing, estimating F-Thresholds and crit exps
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Approximates the F-pure Threshold
--Gives a list of nu_I(p^d)/p^d for d=1,...,e
fptApproximation = method();

fptApproximation ( ZZ, Ideal ) := (e, I) ->
(
     p := char ring I;
     nus := nuList(e,I);
     apply( nus, 1..e, (n,k) -> n/p^k )
)

fptApproximation ( ZZ, RingElement ) := ( e, f ) -> fptApproximation( e, ideal(f) )

--Approximates the F-Threshold with respect to an ideal J
--More specifically, this gives a list of nu_I^J(p^d)/p^d for d=1,...,e

ftApproximation = method();

ftApproximation ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical(J) ) then 
        error "ftApproximation: F-threshold undefined";
    p := char ring I;
    nus := nuList(e,I,J);
    apply( nus, 1..e, (n,k) -> n/p^k )
)

ftApproximation ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> 
   fptApproximation( e, ideal(f), J )

criticalExponentApproximation = method();

criticalExponentApproximation ( ZZ, Ideal, Ideal ) := ( e, I, J ) ->
(
    if not isSubset( I, radical(J) ) then 
        error "criticalExponentApproximation: critical exponent undefined";
    p := char ring I;
    mus := muList( e, I, J );
    apply( mus, 1..e, (n,k) -> n/p^k )
)

criticalExponentApproximation ( ZZ, RingElement, Ideal ) := ( e, f, J ) -> 
    criticalExponentApproximation( e, ideal(f), J )

--Guesses the FPT of ff.  It returns a list of all numbers in 
--the range suggested by nu(e1,ff) with maxDenom as the maximum denominator
guessFPT ={OutputRange=>false}>>o -> (ff, e1, maxDenom) ->
(
    nn := nu(e1,ff);
    pp := char ring ff;
    if (o.OutputRange == false) then 
        findNumberBetween( maxDenom, nn/(pp^e1-1), (nn+1)/(pp^e1) )
    else
        { 
	    { nn/(pp^e1-1), (nn+1)/(pp^e1) }, 
	    findNumberBetween( maxDenom, nn/(pp^e1-1), (nn+1)/(pp^e1) ) 
	}
)

----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------
 
--- Computes the F-signature for a specific value a/p^e
--- Input:
---	f - some polynomial in two or three variables in a ring R of PRIME characteristic
---	a - some positive integer between 0 and p^e
---	e - some positive integer
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Code is based on work of Eric Canton
fSig = ( f, a, e ) -> 
(
     R := ring f;
     p := char R;     
     1 - p^( -e * dim( R ) ) * degree( frobenius( e, maxIdeal R ) + ideal( fastExponentiation( a, f ) ) ) 
)  

--Determines if a pair (R, f^t) is F-regular at a prime
--ideal Q in R, where R is a polynomial ring  
isFRegularPoly = ( f, t, Q ) -> not isSubset( testIdeal( t, f ), Q )

-- F-pure threshold estimation, at the origin.
-- e is the max depth to search in.
-- FRegularityCheck is whether the last isFRegularPoly is run (which can take a significant amount of time). 
-- This is essentially the same as the old estFPT, with a couple more tests, and changes to make the code clearer.
fpt = method( 
    Options => 
        {
	    FRegularityCheck => true, 
	    Verbose => false, 
	    DiagonalCheck => true, 
	    BinomialCheck => true, 
	    BinaryFormCheck => true, 
	    NuCheck => true    	
	}
)

fpt ( RingElement, ZZ ) := QQ => o -> ( f, e ) -> 
(
    -- Check if option values are valid
    checkOptions( o, 
        {
	    FinalCheck => Boolean, 
	    Verbose => Boolean, 
	    DiagonalCheck => Boolean, 
	    BinomialCheck => Boolean, 
	    BinaryFormCheck => Boolean, 
	    NuCheck => Boolean    	
	}
    );

    -- Check if polynomial has coefficients in a finite field
    if not isPolynomialOverFiniteField f  then 
        error "fpt: expected polynomial with coefficients in a finite field";

    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at  
    p := char ring f;
    if not isSubset( ideal f, M ) then 
        error "fpt: polynomial is not in the homogeneous maximal ideal";   

    if o.Verbose then print "\nStarting fpt ...";
    
    -- Check if fpt equals 1
    if not isSubset( ideal( f^(p-1) ), frobenius M ) then 
    (
        if o.Verbose then print "\nnu(1,f) = p-1, so fpt(f) = 1."; 
        return 1 
    );

    if o.Verbose then print "\nfpt is not 1 ...";

    -- Check if one of the special FPT functions can be used...
    
    -- Check if f is diagonal:
    if o.DiagonalCheck and isDiagonal f then 
    ( 
        if o.Verbose then 
	    print "\nPolynomial is diagonal; calling diagonalFPT ..."; 
        return diagonalFPT f 
    );

    -- Now check if f is a binomial:
    if o.BinomialCheck and isBinomial f then 
    ( 
        if o.Verbose then 
	    print "\nPolynomial is a binomial; calling binomialFPT ...";
        return binomialFPT f 
    );

    -- Finally, check if f is a binary form:
    if o.BinaryFormCheck and isBinaryForm f then 
    ( 
        if o.Verbose then 
	    print "\nPolynomial is a binary form; calling binaryFormFPT ...";
        return binaryFormFPT f 
    );
    
    if o.Verbose then print "\nSpecial fpt algorithms were not used ...";
     
    -- Compute nu(e,f)
    n := nu( e, f );
        
    if o.Verbose then
         print( "\nnu has been computed: nu(e,f) = " | toString n | " ..." );
    
    -- If nu = 0, we just return some information
    if n == 0 then 
    (
	if o.Verbose then 
	    print "\nThe nu computed isn't fine enough. Try increasing the max exponent e.";
	return { 0, 1/p^e }
    );

    -- Check to see if either nu/(p^e-1) or (nu+1)/p^e is the fpt
    if o.NuCheck then 
    (
        -- Check to see if nu/(p^e-1) is the fpt
	-- (uses the fact that there are no fpts between nu/p^e and nu/(p^e-1))
	if not isFRegularPoly( f, n/(p^e-1), M ) then 
	(
	    if o.Verbose then print "\nFound answer via nu/(p^e-1)."; 
	    return n/(p^e-1)
	) 
      	else if o.Verbose then print "\nnu/(p^e-1) is not the fpt ...";
	
        --check to see if (nu+1)/p^e is the FPT
	if isFPT( (n+1)/p^e, f ) then 
	(
	    if o.Verbose then print "\nFound answer via (nu+1)/(p^e)."; 
	    return (n+1)/p^e
	) 
      	else if o.Verbose then print "\n(nu+1)/p^e is not the fpt ..."
    );

    -- Do the F-signature computation
    local s1;
    local s2;
    
    if o.Verbose then print "\nBeginning F-signature computation ...";
    s2 = fSig( f, n, e );
    if o.Verbose then 
        print( "\nFirst F-signature computed: s(f,nu/p^e) = " | toString s2 | " ..." );
    s1 = fSig( f, n-1, e );
    if o.Verbose then 
	print( "\nSecond F-signature computed: s(f,(nu-1)/p^e) = " | toString s1 | " ..." );
	
    a := xInt( (n-1)/p^e, s1, n/p^e, s2 );
    
    if o.Verbose then 
        print( "\nComputed F-signature intercept: " | toString a | " ..." );

    -- Now check to see if F-signature line crosses at (nu+1)/p^e. If so, then that's the fpt
    if (n+1)/p^e == a then 
    (
	if  o.Verbose then 
	    print "\nF-signature line crosses at (nu+1)/p^e, so that is the fpt."; 
	return a
    );
	       	
    if o.FRegularityCheck then 
    (
	if o.Verbose then print "\nStarting final check ..."; 
        if not isFRegularPoly( f, a, M ) then 
        (	
	   if o.Verbose then 
	       print "\nFinal check successful; fpt is the F-signature intercept."; 
	   return a
      	)
	else if o.Verbose then print "\nFinal check didn't find the fpt ..."
    );

    if o.Verbose then 
        print(
	    "\nfpt lies in the interval " |
	    ( if o.FRegularityCheck then "( " else "[ " ) |  
	    toString a | 
	    ", " | 
	    toString( (n+1)/p^e ) | 
	    ( if o.NuCheck then " )." else " ]." ) 
        );    
    { a, (n+1)/p^e }
)

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for checking if given numbers are F-jumping numbers
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--isFPT, determines if a given rational number is the FPT of a pair in a 
-- polynomial ring. 

isFPT = method( Options => { Verbose=> false } )

isFPT ( QQ, RingElement ) := o -> ( t, f ) -> 
(
    R := ring f;
    p := char R;
    --this writes t = a/(p^b(p^c-1))
    (a,b,c) := toSequence decomposeFraction( p, t );

    -- sigma
    a1 := if c == 0 then a-1 else floor( (a-1)/(p^c-1) );
    Sigma := if c == 0 then sigma( f, p-1, 1 ) 
        else sigma( f, ( (a-1)%(p^c-1) ) + 1, c );	
    if o.Verbose then print "\nSigma Computed";
	
    if not isSubset( ideal 1_R, frobeniusRoot( b, a1, f , Sigma ) ) then
        return false; 

    if o.Verbose then print "\nWe know t <= FPT";
    
    -- Higher tau
    a2 := if c == 0 then a else floor( a /(p^c-1) );
    Tau := if c == 0 then ideal 1_R else testIdeal( fracPart( a/(p^c-1) ), f );
    if o.Verbose then print "\nHigher tau Computed";
    
    not isSubset( ideal 1_R, frobeniusRoot( b, a2, f, Tau ) )
)

isFPT ( ZZ, RingElement ) := o -> ( t, f ) -> isFPT( t/1, f, o )

-- isFJumpingNumber determines if a given rational number is an 
-- F-jumping number
--***************************************************************************
--This needs to be speeded up, like the above function
--***************************************************************************

isFJumpingNumber = method( Options => {Verbose=> false} )

isFJumpingNumber ( QQ, RingElement ) := o -> ( t, f ) -> 
(
    p := char ring f;
    --this writes t = a/(p^b(p^c-1))
    (a,b,c) := toSequence decomposeFraction( p, t );
    Tau := frobeniusRoot( b, testIdeal( t*p^b, f ) );
    if o.Verbose then print "\nHigher tau Computed";

    local Sigma;
    if c == 0 then
        Sigma = frobeniusRoot( b, ideal( f^(a-1) ) * sigma( f, p-1, 1 ) )
    else Sigma = frobeniusRoot( b, sigma( f, a, c ) );
    if o.Verbose then print "\nSigma Computed";

    -- if sigma is not contained in tau, this is an F-jumping number
    not isSubset( Sigma, Tau )
)

isFJumpingNumber ( ZZ, RingElement ) := o -> ( t, f ) -> 
    isFJumpingNumber( t/1, f, o )


----------------------------------------------------------------
--************************************************************--
--Functions for computing sigma                               --
--************************************************************--
----------------------------------------------------------------

--Computes Non-Sharply-F-Pure ideals over polynomial rings for 
-- (R, f^{a/(p^{e}-1)}), at least defined as in Fujino-Schwede-Takagi.
sigma = ( f, a, e ) -> 
(
    R := ring f;
    p := char R;
    m := 0;
    e1 := e;
    a1 := a;
    --if e = 0, we treat (p^e-1) as 1.  
    if e1 == 0 then 
        (
	    e1 = 1; 
	    a1 = a*(p-1)
	);
     if a1 > p^e1-1 then 
         (
	     m = floor( (a1-1)/(p^e1-1) ); 
	     a1 = (a1-1)%(p^e1-1) + 1 
	 );
     --fpow := f^a1;
     IN := frobeniusRoot( e1, ideal 1_R ); -- this is going to be the new value.
     IP := ideal 0_R; -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  
     -- This stops after finitely many steps.  
     while IN != IP do
     (
	 IP = IN;
	 IN = frobeniusRoot( e1, a1, f, IP ); -- ethRoot(e1,ideal(fpow)*IP);
	 count = count + 1
     );

     --return the final ideal
    IP*ideal( f^m )
)
