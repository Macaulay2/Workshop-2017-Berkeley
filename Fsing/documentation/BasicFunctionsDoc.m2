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
	   Computes the base p expansion of an integer N:  the output is a list in which the i-th element is the coefficient of p^i.
	   Computes the first e digits in the unique non-terminating base p expansion of a positive rational number x in the unit interval: the output is a list in which the i-th element is the coefficient of p^(-i-1).	    
	    
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
             This differs from floor(log_b(x)), in that it corrects problems due to rounding.
         Example
             floor( log_3 3^5 )
             floorLog( 3, 3^5 )
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

 
 
