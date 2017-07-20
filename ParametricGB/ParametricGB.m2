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


-- We followed the definition in Weispfenning1992 paper.
color = memoize ((f,gamma) -> (
    Z:=gamma_0;
    NZ:=gamma_1;
    a:=leadCoefficient(f);
    K:=coefficientRing(ring a);    
    if Z != {} then a = a % (ideal(Z));
    if a==0 then return "green";
    for j from 0 to #NZ-1 do (
        while (a % ideal(NZ_j))==0 do a = lift(a/(NZ_j),ring(a))
    );
    if monomials(a)==matrix {{1_(ring a)}} then return "red" else return "white"
));

--We removed green parts and divided by all possible red parts.
reducedPart = memoize ((f,gamma) -> (
    Z:=gamma_0;
    NZ:=gamma_1;
    a:=leadCoefficient(f);    
    if Z != {} then a = a % (ideal(Z));
    for j from 0 to #NZ-1 do (
        while (a % ideal(NZ_j))==0 do a = lift(a/(NZ_j),ring(a))
    );
    return a    
));

-- Terms and Monomials are used reversed in the paper and Macaulay 2.
headMonomial = memoize ((f,gamma) -> (
    g:=leadTerm(f);
    while color(g,gamma)=="green" do (
	f = f-g;
	g=leadTerm(f);
	if g==0 then return {g,"green"}
    );
    return {leadTerm(f),color(f,gamma)}
));

determineCover = memoize ((f,GGamma) -> (
    g := 0;
    refinedGamma := {};
    tempList := {};
    if GGamma == {} then GGamma = {{{},{}}};
    for j from 0 to #GGamma-1 do(
	g = headMonomial(f,GGamma_j);
        if g_1 == "white" then (
	    tempList = {append(GGamma_j_1,reducedPart(g_0,GGamma_j))};
	    tempList = insert(0,GGamma_j_0,tempList);
	    refinedGamma = append(refinedGamma,tempList);
	    tempList = {append(GGamma_j_0,reducedPart(g_0,GGamma_j))};
	    tempList = insert(1,GGamma_j_1,tempList);
	    refinedGamma = join(refinedGamma,determineCover(f,{tempList}))
        )
        else refinedGamma = append(refinedGamma,GGamma_j);
    );
    return unique(refinedGamma)
));

determineCoverF = (F,GGamma) -> (
    for f in F do (
	GGamma = determineCover(f,GGamma)
    );
    return GGamma
);

hDividesT = (h,t) -> (
    e1 := first exponents(h);
    e2 := first exponents(t);
    for i from 0 to #e1-1 do (
	if e1_i > e2_i then return false
    );
    return true
);

tOverh = (t,h) -> (
    e1 := first exponents(t);
    e2 := first exponents(h);
    R := ring(t);
    return product apply(#e1,i->(R_i)^(e1_i-e2_i))
);


reducedByP = (f,p,gamma) -> (
    h := headMonomial(p,gamma);
    a := 0;
    t := 0;
    s := 0;
    if h_1 == "white" or h_1 == "green" then return f;
    h = h_0;
    for u in terms(f) do (
	if color(u,gamma) == "red" or color(u,gamma) == "white" then (
    	    a = leadCoefficient(u);
	    t = leadMonomial(u);
	    if hDividesT(leadMonomial(h),t) then (
		s = tOverh(t,h); 
	        f = leadCoefficient(h)*f - a*s*p
	    );
	);
    );
    return f;
);

normalForm = (f,P,gamma) -> (
    g := f;
    c := 1;
    for p in P do (
	g = reducedByP(g,p,gamma);
	c = c*leadCoefficient(first headMonomial(p,gamma))
    );
    return {g,c}
);

sPol = (f,g,gamma) -> (
    s := first headMonomial(f,gamma);
    a := leadCoefficient(s);
    s = leadMonomial(s);
    t := first headMonomial(g,gamma);
    b := leadCoefficient(t);
    t = leadMonomial(t);
    e1 := first exponents(s);
    e2 := first exponents(t);
    R := ring(s);
    u := product apply(#e1, i -> (R_i)^(max(e1_i,e2_i)-e1_i));
    v := product apply(#e2, i -> (R_i)^(max(e1_i,e2_i)-e2_i));
    return b*u*f - a*v*g
);




groebnerSystem = (F,B) -> (
    GGamma := flatten apply(B,b -> determineCoverF(F,{b}));
    GS := apply(GGamma, i -> {i,F});
);

-- Examples to test
R=QQ[c_1,c_2][x_0,x_1,x_2,x_3]
Z={c_1}
NZ={c_2}
empty = {{},{}}
gamma = {Z,NZ}
f1 = c_1^2*(c_1+2*c_2)*x_0*x_1
f2 = c_2^2*(c_1+2*c_2)*x_0*x_2
f3 = c_2^2*(c_2+2)*x_0*x_3
f4 = x_0
color(f4,{{},{}})
color(f2,gamma)
color(f3,gamma)
color(f1,gamma)
headTerm(f1+f2,gamma)
headTerm(f1+f3,gamma)
determineCover(f1+f2,)
determineCover(f1+f2+f3,determineCover(f1+f3,{gamma}))
reducedByP(f1,f2,gamma)
tOverh(t,h)
normalForm(f1,{f1},gamma)
sPol(f2,f3+f2,gamma)
B = {{{},{}}}
F = {f1,f2,f3}


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
