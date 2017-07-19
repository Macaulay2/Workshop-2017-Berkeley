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
    "fakeParametricGB"
    }

square = method(
    TypicalValue => ZZ
)


square(ZZ) := (x) -> (x^2)


fakeParametricGB = method(
    TypicalValue => List    
)



fakeParametricGB(Ideal) := (I) -> (
    return ///{
    { {}, {c_2,c_1,c_1-c_2},  matrix {{ x_0^2*x_3^2*c_1^3 - x_0^2*x_3^2*c_1^2*c_2,x_0*x_1*x_3*c_1^2 - x_0*x_1*x_3*c_1*c_2,x_0*x_2*x_3*c_1^2 - x_0*x_2*x_3*c_1*c_2, x_1^2*c_2 - x_0*x_2*c_1, x_1*x_2*c_2 - x_0*x_3*c_1, x_2^2*c_2 - x_1*x_3*c_1}}},
    { {c_2}, {c_1}, matrix {{x_0*x_2*c_1,x_0*x_3*c_1,x_1*x_3*c_1}}},
    { {c_1,c_2}, {}, map((ring I)^1,(ring I)^0,0)},
    { {c_1}, {c_2}, matrix {{ x_1^2*c_2, x_1*x_2*c_2, x_2^2*c_2}}},
    { {c_1-c_2}, {c_1,c_2}, matrix {{x_1^2*c_2 - x_0*x_2*c_2,x_1*x_2*c_2 - x_0*x_3*c_2,x_2^2*c_2 - x_1*x_3*c_2}}},
    }///
)
 



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

doc ///
    Key
        fakeParametricGB
	(fakeParametricGB,Ideal)
    Headline
        demonstrates what we want
    Usage
        fakeParametricGB(I)
    Inputs
        I:Ideal
    Outputs
        L:List
	    the parametric Groebner basis    
    Description
        Text
	    This function is fake.  It computes nothing.  It demonstrates the input/output we want.
	      
        Example
            R=QQ[c_1,c_2][x_0,x_1,x_2,x_3]
            I = ideal {c_1*x_0*x_2-c_2*x_1^2,c_1*x_0*x_3-c_2*x_1*x_2,c_1*x_1*x_3-c_2*x_2^2}
            fakeParametricGB(I)
///

TEST ///
    assert(square(4)=== 16)
///


endPackage "ParametricGB" 



end

uninstallPackage("ParametricGB")
restart
installPackage("ParametricGB")

loadPackage("ParametricGB")

check "ParametricGB"
