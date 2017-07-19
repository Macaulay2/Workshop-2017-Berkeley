"carryTest",  
    "adicExpansion",    
    "digit", 	   
    "denom",   
    "divideFraction",
    "firstCarry", 
    "floorLog",
    "fracPart", 
    "getCanVector",
    "getNumAndDenom", 
    "maxIdeal", 
    "multOrder",
    "num",
    "taxicabNorm",
    "truncatedBasePExp",
    
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
     	 Computes base p expansions.
     Usage
     	 adicExpansion(p,N)
	 adicExpansion(p,e,x)
     Inputs 
     		p:ZZ
		N:ZZ	
		e:ZZ
		x:QQ	
     Outputs
         :List
     Description
	Text
	   adicExpansion(p,N) computes the base p expansion of an integer N:  the output is a list in which the i-th element is the coefficient of p^i.
    	Example
	    Since 5=1*2^0+0*2^1+1*2^2, adicExpansion(2,5) = {1,0,1}.
	Text
           adicExpansion(p,e,x) Computes the first e digits in the unique non-terminating base p expansion of a positive rational number x in the unit interval: the output is a list in which the i-th element is the coefficient of p^(-i-1).	    
	Example 
	    The unique non-terminating base 2 expansion of 1/2 is 1/2 = 0/2 + 1/4 + 1/8 + 1/16 + ..., and so adicExpansion(2,4,1/2) = {0, 1, 1, 1}.     
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
		x:ZZ		
     Outputs
         :ZZ
     Description
	Text
	    This differs from floor(log_b(x)) in that it corrects problems due to rounding.
/// 

doc ///
     Key
     	multOrder
     	(multOrder, ZZ, ZZ)
     Headline
        Computes the multiplicative order of a modulo b
     Usage
     	 multOrder(a,b)
     Inputs 
     		a:ZZ
		b:ZZ		
     Outputs
         :ZZ
     Description
	Text
	    This computes the multiplicative order of a modulo b.  If a and b are not relatively prime, it returns an error.
///

 
 
