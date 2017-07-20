--*************************************************
--*************************************************
--*************************************************
--*************************************************
--This file is used for doing basic computations 
--i.e. things using only lists, numbers, etc.
-- that support other functions in the Fsing
--package.  
--*************************************************
--*************************************************
--*************************************************
--*************************************************

--*************************************************
--Basic Manipulations with Numbers 
--*************************************************
--===================================================================================

denominator( ZZ ) := x -> 1

numerator( ZZ ) := x -> x

--===================================================================================

--Finds the fractional part of a number.
fracPart = x -> x - floor(x)

--===================================================================================

--Computes floor(log_b x), correcting problems due to rounding.
floorLog = method( TypicalValue => ZZ )

floorLog ( ZZ, ZZ ) := ZZ => ( b, x ) -> 
(
    if b <= 1 then error "floorLog: expected the first argument to be greater than 1";
    if x <= 0 then error "floorLog: expected the second argument to be positive";
    if x < b then return 0;
    flog := floor( log_b x );
    while b^flog <= x do flog = flog + 1;
    flog - 1       
)

--===================================================================================

multOrder = method( TypicalValue => ZZ )

--Finds the multiplicative order of a modulo b.
multOrder( ZZ, ZZ ) := ZZ => ( a, b ) ->
(
    if gcd( a, b ) != 1 then error "multOrder: Expected numbers to be relatively prime.";
    n := 1;
    x := 1;
    while (x = (x*a) % b) != 1 do n = n+1;
    n	      
)     

--===================================================================================

divideFraction = method( TypicalValue => List, Options => { NoZeroC => false } );

-- This function takes in a fraction t and a prime p and spits out a list
-- {a,b,c}, where t = a/(p^b*(p^c-1))
-- if c = 0, then this means that t = a/p^b
--alternately, if NoZeroC => true, then we will always write t = a/p^b(p^c - 1)
--even if it means increasing a. 
divideFraction( ZZ, QQ ) := List => o -> ( p, t ) -> 
(
    if not isPrime( p ) then error "divideFraction: first argument must be a prime number.";
    a := numerator t; -- finding a is easy, for now
    den := denominator(t);
    b := 1;
    while den % p^b == 0 do b = b+1;
    b = b-1; 
    temp := denominator( t*p^b );
    local c;
    if (temp == 1) then c = 0 else 
    (
        c = multOrder( p, temp );  
        a = lift( a*(p^c-1)/temp, ZZ ); -- fix a
    );
    if o.NoZeroC and c == 0 then 
    (
        a = a*(p-1);
        c = 1;
    );
    {a,b,c}
)

divideFraction( ZZ, ZZ ) := List => o -> (p, t) -> divideFraction(p, t/1, o)


--===================================================================================

--*************************************************
--Base p-expansions
--*************************************************

--===================================================================================

adicDigit = method( TypicalValue => ZZ )

--Gives the e-th digit of the non-terminating base p expansion of x in (0,1].
digit ( ZZ, ZZ, QQ ) := ZZ => ( p, e, x ) -> 
(
    if x < 0 or x > 1 then error "adicDigit: Expected x in [0,1]";     
    if x == 0 then return 0;	
    local y;
    if fracPart( p^e*x ) != 0 then y = floor( p^e*x ) - p*floor( p^(e-1)*x );
    if fracPart( p^e*x ) == 0 then y = floor( p^e*x ) - p*floor( p^(e-1)*x ) - 1;
    if fracPart( p^(e-1)*x ) == 0 then y = p-1;
    y	  
)

--Creates list containing e-th digits of non-terminating base p expansion of list of numbers.
adicDigit ( ZZ, ZZ, List ) := ZZ => ( p, e, u ) -> apply( u, x -> adicDigit( p, e, x ) )

--===================================================================================

adicExpansion = method( TypicalValue => List ); 

--Computes the terminating base p expansion of a positive integer.
--Gives expansion in reverse... so from left to right it gives
--the coefficient of 1, then of p, then of p^2, and so on

adicExpansion( ZZ, ZZ ) := List => ( p, N ) ->
(
    if p <= 0 then error "adicExpansion: Expected first argument to be positive";
    if N < 0 then error "adicExpansion: Expected second argument to be nonnegative";
    if N < p then { N } else prepend( N % p, adicExpansion( p, N // p ) ) 
    -- would this be faster if it were tail-recursive? we could do this w/ a helper function.
)

--Creates a list of the first e digits of the non-terminating base p expansion of x in [0,1].
adicExpansion( ZZ, ZZ, QQ ) := List => ( p, e, x ) -> 
(
    if x < 0 or x > 1 then error "adicExpansion: Expected x in [0,1]";
    apply( e, i -> adicDigit( p, i+1, x ) )
)

--===================================================================================

truncatedBasePExp = method( TypicalValue => QQ )

--Gives the e-th truncation of the non-terminating base p expansion of a rational number.
truncatedBasePExp ( ZZ, ZZ, QQ ) := QQ => ( p, e, x ) -> 
(
    if x <= 0 then error "truncatedBasePExp: Expected x>0";
    ( ceiling( p^e*x ) - 1 )/p^e    	
)

--truncation threads over lists.
truncatedBasePExp ( ZZ, ZZ, List ) := List => ( p, e, u ) -> 
    apply( u, x -> truncatedBasePExp( p, e, x ) )

--===================================================================================

--- write n=a*p^e+a_{e-1} p^{e-1} + \dots + a_0 where 0\leq a_j <p 
--- DS: so it's just like doing adicExpansion but giving up after p^e and just returning whatever number's left
--- DS: this could be merged with adicExpansion. Should it be? 
--- note: I changed the calling order here should change to be consistent with adicExpansion
--- The change I made was switching the order of the first two arguments
baseP1 = ( p, n, e ) ->
(
    a:=n//(p^e);
    answer:=1:a; -- this generates the list (a)
    m:=n-a*(p^e);
    f:=e-1; 
    while (f>=0) do
    (
        d:=m//(p^f);
        answer=append(answer,d);
        m=m-d*(p^f);
        f=f-1;
    );
    answer
)	

--===================================================================================

--*************************************************
--Tests for various types of polynomials   
--*************************************************

--===================================================================================

--isPolynomial(F) checks if F is a polynomial
isPolynomial = method( TypicalValue => Boolean )

isPolynomial (RingElement) := Boolean => F -> isPolynomialRing( ring F ) 

--===================================================================================

--isPolynomialOverPosCharField(F) checks if F is a polynomial over a field
--of positive characteristic
isPolynomialOverPosCharField = method( TypicalValue => Boolean )

isPolynomialOverPosCharField (RingElement) := Boolean => F ->
    isPolynomial F and isField( kk := coefficientRing ring F ) and ( char kk ) > 0

--===================================================================================

--isPolynomialOverFiniteField(F) checks if F is a polynomial over a finite field.
isPolynomialOverFiniteField = method( TypicalValue => Boolean )

-- This was reverted so that users with older M2 version could load 

--isPolynomialOverFiniteField (RingElement) := Boolean => F ->
--    isPolynomialOverPosCharField( F ) and isFinitePrimeField(coefficientRing ring F)

isPolynomialOverFiniteField (RingElement) := Boolean => F ->
    isPolynomialOverPosCharField( F ) and  ( try (coefficientRing ring F)#order then true else false )
--===================================================================================

--*************************************************
--Partitions
--*************************************************

---------------------------------------------------------------------------------------
--- The following code was written in order to more quickly compute eth roots of (f^n*I)
--- It is used in fancyEthRoot
----------------------------------------------------------------------------------------
--- Find all ORDERED partitions of n with k parts
allPartitions = ( n, k )->
(
	PP0:=matrix{ toList(1..k) };
	PP:=mutableMatrix PP0;
	allPartitionsInnards (n,k,PP,{})
)

allPartitionsInnards = ( n, k, PP, answer)->
(
	local i;
	if (k==1) then 
	(
		PP_(0,k-1)=n;
		answer=append(answer,first entries (PP));
	)
	else
	(
		for i from 1 to n-(k-1) do
		(
			PP_(0,k-1)=i;
			answer=allPartitionsInnards (n-i,k-1,PP,answer)	;	
		);
	);
	answer
)

--===================================================================================

--*************************************************
--Miscelaneous
--*************************************************

--===================================================================================

-- maxIdeal returns the ideal generated by the variables of a polynomial ring
maxIdeal = method( TypicalValue => Ideal )

maxIdeal ( PolynomialRing ) := Ideal => R -> monomialIdeal R_*

maxIdeal ( RingElement ) := Ideal => f -> maxIdeal ring f

maxIdeal ( Ideal ) := Ideal => I -> maxIdeal ring I

--===================================================================================

