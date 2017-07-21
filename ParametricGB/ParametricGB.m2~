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

color = method(
    TypicalValue => String    
)



color =(f,gamma) -> (
    Z:=gamma_0;
    NZ:=gamma_1;
    a:=leadCoefficient(f);
    K:=coefficientRing(ring a);    
    a = a % (ideal(Z));
    if a==0 then return "green";
    for j from 0 to #NZ-1 do (
        while (a % ideal(NZ_j))==0 do a = lift(a/(NZ_j),ring(a))
    );
    if monomials(a)==matrix {{1_(ring a)}} then return "red" else return "white"
)

headTerm = (f,gamma) -> (
    g:=leadTerm(f);
    while color(g,gamma)=="green" do (
	f = f-g;
	g=leadTerm(f);
	if g==0 then return {g,"green"}
    );
    return {leadTerm(f),color(f,gamma)}
);

determineCover = (f,gamma) -> (
    g := headTerm(f,gamma_0);
    refinedGamma := {};
    tempList := {};
    for j from 0 to #gamma-1 do(
	g = headTerm(f,gamma_j);
        if g_1 == "white" then (
	    tempList = {append(gamma_j_1,leadCoefficient(g_0))};
	    tempList = insert(0,gamma_j_0,tempList);
	    refinedGamma = append(refinedGamma,tempList);
	    tempList = {append(gamma_j_0,leadCoefficient(g_0))};
	    tempList = insert(1,gamma_j_1,tempList);
	    refinedGamma = join(refinedGamma,determineCover(f,{tempList}))
        )
        else refinedGamma = append(refinedGamma,gamma_j);
    );
    return refinedGamma
);


-- Examples to test
R=QQ[c_1,c_2][x_0,x_1,x_2,x_3]
Z={c_1}
NZ={c_2}
gamma = {Z,NZ}
f1 = c_1^2*(c_1+2*c_2)*x_0*x_1
f2 = c_2^2*(c_1+2*c_2)*x_0*x_2
f3 = c_2^2*(c_2+2)*x_0*x_3
color(f1,gamma)
color(f2,gamma)
color(f3,gamma)
headTerm(f1+f2,gamma)
headTerm(f1+f3,gamma)
determineCover(f1+f3,{gamma})


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
