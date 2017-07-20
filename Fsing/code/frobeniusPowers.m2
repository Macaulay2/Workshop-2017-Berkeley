--*************************************************
--*************************************************
--This file is used for taking various types of 
--powers of ideals in characteristic p>0. 
--*************************************************
--*************************************************



--Computes powers of elements in char p>0, using that Frobenius is an endomorphism. If 
--N = N_0 + N_1 p + ... + N_e p^e, where 0 <= N_i < p, then this computes f^N as
--f^(N_0) (f^(N_1))^p ... (f^(N_e))^(p^e). 

fastExp = method( TypicalValue => RingElement )

fastExp ( ZZ, RingElement ) := RingElement => ( N, f ) ->
(
    if N < 0 then error "fastExp: first argument must be a polynomial over a nonnegative integer.";
    if char ring f == 0 then 
        error "fastExp: second argument must be a polynomial over a field of positive characteristic.";
    p:=char ring f;
    E:=adicExpansion(p,N);
    product(#E, e -> sum( terms f^(E#e), g -> g^(p^e) ) )
)

--------------------------------------------------------------------------------------------------------

--Outputs the p^e-th Frobenius power of an ideal, or the p^e-th (entry-wise) Frobenius power of a matrix.

frobeniusMethod =  method( TypicalValue => Ideal, Options => { FrobeniusRootStrategy => Substitution } );

frobeniusMethod ( ZZ, Ideal ) := Ideal => o -> ( e, I ) ->
(
    R := ring I;
    p := char R;
    if p == 0 then 
        error "frobeniusMethod: expected an ideal in a ring of positive characteristic.";
    if e == 0 then return I;
    if e < 0 then return frobeniusRoot( -e, I, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
    G := I_*;
    if #G == 0 then ideal( 0_R ) else ideal( apply( G, j -> fastExp( p^e, j ) ) )
)

frobeniusMethod ( ZZ, Matrix ) := Matrix => o -> ( e, M ) ->
(
    p := char ring M;
    if p == 0 then 
        error "frobeniusMethod: expected an matrix with entries in a ring of positive characteristic.";
    if e == 0 then return M;
    if e < 0 then error "frobenius: first argument must be nonnegative.";
    matrix apply( entries M, u -> apply( u, j -> fastExp( p^e, j ) ) )
)

frobeniusMethod ( Ideal ) := Ideal => o -> I -> frobeniusMethod( 1, I, o )

frobeniusMethod ( Matrix ) := Matrix => o -> M -> frobeniusMethod( 1, M )

FrobeniusOperator = new Type of MethodFunctionWithOptions

frobenius = new FrobeniusOperator from frobeniusMethod

FrobeniusOperator ^ ZZ := ( f, n ) -> ( x -> f( n, x ) )

--------------------------------------------------------------------------------------------------------

--This is an internal function.  Given ideals I,J and a positive integer e, consider
--the following chain of ideals:
--K_1 = (I*J)^[1/p^e] and K_{s+1} = (I*K_s)^[1/p^e]
--This chain is ascending, and has the property that once two consecutive terms
--agree, the chain stabilizes.  This function outputs the stable ideal of this chain.

stableIdeal = { FrobeniusRootStrategy => Substitution } >> o -> ( e, I, J ) -> 
(
    K := ideal( 0_( ring I ) );
    L := frobeniusRoot( e, I*J, o );
    while not isSubset( L, K ) do
    (
    	K = L;              
    	L = frobeniusRoot( e, I*K, o );
    );
    trim K 
)

--------------------------------------------------------------------------------------------------------

--Outputs the generalized Frobenius power of an ideal; either the N-th Frobenius power of N/p^e-th one.

frobeniusPower = method( Options => { FrobeniusPowerStrategy => Naive, FrobeniusRootStrategy => Substitution } );

--Computes the integral generalized Frobenius power I^[N]
frobeniusPower ( ZZ, Ideal ) := opts -> ( N, I ) -> 
(
     R := ring I;
     p := char R;
     G := first entries mingens I;
     if #G == 0 then return ideal( 0_R );
     if #G == 1 then return ideal( fastExp( N, G#0 ) );
     E := adicExpansion( p, N );
     product( #E, m -> frobenius( m, I^( E#m ) ) )
)

--Computes the generalized Frobenius power I^[N/p^e]
frobeniusPower( ZZ, ZZ, Ideal ) := opts -> ( e, N, I ) ->
(
     R := ring I;
     p := char R;
     G := first entries mingens I;
     if #G == 0 then return ideal( 0_R );
     rem := N % p^e;
     M := N // p^e;
     J := frobeniusPower( M, I );  --component when applying Skoda's theorem
     
    if opts.FrobeniusPowerStrategy == Safe then 
    (
	E := adicExpansion( p, rem );
	J * product( #E, m -> frobeniusRoot( e-m, I^( E#m ),  FrobeniusRootStrategy => opts.FrobeniusRootStrategy ) );  --step-by-step computation of generalized Frobenius power of I^[rem/p^e]
                                                                            --using the base p expansion of rem/p^e < 1
    )
    else J * frobeniusRoot( e, frobeniusPower( rem, I ), FrobeniusRootStrategy => opts.FrobeniusRootStrategy )  --Skoda to compute I^[N/p^e] from I^[rem/p^e] 
)

--Computes the generalized Frobenius power I^[t] for a rational number t 
frobeniusPower( QQ, Ideal ) := opts -> ( t, I ) ->
(
    p := char ring I;
    ( a, b, c ) := toSequence divideFraction( p, t ); --write t = a/(p^b*(p^c-1))
     if c == 0 then frobeniusPower( b, a, I, opts )  --if c = 0, call simpler function
    	else 
	(
	    rem := a % ( p^c - 1 );      
	    quot := a // ( p^c - 1 );     
	    J := stableIdeal( c, frobeniusPower( rem, I ), I, FrobeniusRootStrategy => opts.FrobeniusRootStrategy );
	    frobeniusRoot( b, frobeniusPower( quot, I ) * J, FrobeniusRootStrategy => opts.FrobeniusRootStrategy )
        )
)
