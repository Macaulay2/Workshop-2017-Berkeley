-- -*- coding: utf-8 -*-
-- licensed under GPL v2 or any later version
newPackage(
    "ParametricGB",
    Version => "0.4",
    Date => "May 13, 2017",
    Headline => "Common types for Lie groups and Lie algebras",
    Authors => {
	  {Name => "Dave Swinarski", Email => "dswinarski@fordham.edu"}
	  }
    )

export {
    --for the LieAlgebra type:
    "square",
    }

square(ZZ) := (x) -> (x^2)


beginDocumentation()





doc ///
    Key
        square
	(square,ZZ)
    Headline
        squares an integer
    Usage
        square(n)
    Inputs
        n:ZZ
    Outputs
        m:ZZ
	    the square of n
    Description
        Text
	    This is a silly function.
	      
        Example
	    square(4)	
///

TEST ///
    assert(square(4)=== 16)
///



endPackage "ParametricGB" 
