--***********************************************
--***********************************************
--Documentation for BasicFunctions.m2
--***********************************************
--***********************************************

doc ///
    Key
        adicExpansion
        (adicExpansion, ZZ, ZZ)
        (adicExpansion, ZZ, ZZ, QQ)
    Headline
        computes base p expansions
    Usage
        adicExpansion(p,N)
        adicExpansion(p,e,x)
    Inputs 
        p:ZZ
	    positive
        N:ZZ
	    positive	
        e:ZZ
	    positive
        x:QQ
	    in the interval [0,1]	
    Outputs
        :List
    Description
        Text
            adicExpansion(p,0) returns a list with one element, which is zero.  If N is nonzero, then adicExpansion(p,N) returns a list in which the i-th element is the coefficient of p^i in the base p expansion of N.  
        Example
            5==1*2^0+0*2^1+1*2^2
            adicExpansion(2,5)
        Text
            adicExpansion(p,e,0) returns a list with e elements, all of which are zero.  If x is nonzero, then adicExpansion(p,e,x) returns a list of size e in which the i-th element is the coefficient of p^(-i-1) in the unique nonterminat base p expansion of x.	    
        Text 
            For example, the non-terminating base 2 expansion of 1/2 is 1/2 = 0/2 + 1/4 + 1/8 + 1/16 + ..., and so 
        Example
            adicExpansion(2,4,1/2)
///

doc ///
    Key
        floorLog
    Headline
        Computes the floor of the log base b of x
    Usage
     	floorLog(b,x)         
    Inputs
        b:ZZ
            greater than 1
        x:ZZ
	    positive
    Outputs
        :ZZ
    Description
        Text
            floorLog(b,x) computes floor(log_b(x)), correcting occasional errors due to rounding.
        Example
            floor( log_3 3^5 )
            floorLog( 3, 3^5 )
/// 
    
doc ///
    Key
        multOrder
     	(multOrder, ZZ, ZZ)
    Headline
        computes the multiplicative order of an integer modulo another
    Usage
     	multOrder(a,b)
    Inputs
        a:ZZ
        b:ZZ
            prime to a		
    Outputs
        :ZZ
    Description
        Text
	    This computes the multiplicative order of a modulo b.  If a and b are not relatively prime, it returns an error.
///

doc ///
    Key
        divideFraction
        (divideFraction, ZZ, QQ)
        (divideFraction, ZZ, ZZ)
    Headline
        decomposes a rational number
    Usage
        L = divideFraction(p,t)
        L = divideFraction(p,n)
    Inputs
        p:ZZ
            a prime
        t:QQ
        n:ZZ		
    Outputs
        L:List
    Description
        Text
            Given a rational number t and a prime p, divideFraction(p,t) returns a list {a,b,c} of nonnegative integers such that t = a/(p^b*(p^c-1)).
        Example
            divideFraction( 3, 4/45 )
	    4/45 == 64/( 3^2 * ( 3^4 -1 ) )
        Text
            If c = 0, then t = a/p^b.
        Example
            divideFraction( 3, 4/27 )
        Text
            The option NoZeroC => true forces the third component of the output to be nonzero, even if that means increasing the first component.
        Example
            divideFraction( 3, 4/27, NoZeroC => true )
	    4/27 == 8/( 3^3 * ( 3 - 1 ) )
///

 
 
