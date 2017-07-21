newPackage(
        "CoreIdeal",
        Version => "1.0",
        Date => "July 19, 2017",
        Authors => {{Name => "",
                  Email => "",
                  HomePage => ""}},
        Headline => "an example Macaulay2 package",
        PackageExports => {"LocalRings","randomIdeal"},
        DebuggingMode => true,
        AuxiliaryFiles => true
        )
	
export {}

-- Justin:
-- most of the time zero
-- if Artinian, almost guaranteed not to be zero
-- if I is artinian, mono(I) is gorenstein
-- <=> mono(I) is a complete intersection
-- <=> I=m^b?!?!??!
mono = method()
mono Ideal := Ideal => I -> (
    R := ring I;
    T := local T;
    N := numgens R;
    S := (coefficientRing R)(monoid [gens R, T_{0}..T_{N-1}]);
    G := sub(gens I, S);
    use S;
    for i from 0 to N-1 do
        G = homogenize(G, T_{i}, 
            apply(N, j -> if i==j then 1 else 0) | 
            apply(N, j -> if i==j then 1 else 0));
    use R;
    J := ideal G;
    K := saturate(J, apply(N, i -> T_{i})//product);
    sub(eliminate(apply(N, i->T_{i}), K), R)
    )


monoG = (I) -> (
    t := local t;
    R := ring I;
    X := generators R;
    k := coefficientRing R;
    S := k( monoid [t, X, MonomialOrder => Eliminate 1]);
    J := substitute(I, S);
    scan(#X, i -> (
              w := {1} | toList(i:0) | {1} | toList(#X-i-1:0);
              J = ideal homogenize(generators gb J, (generators S)#0, w);
              J = saturate(J, (generators S)#0);
              J = ideal selectInSubring(1, generators gb J);
              ));
    monomialIdeal substitute(J, R)
    )

randLocal = (I,n) -> (
    R := ring I;
    m := ideal gens R;
    J := randomCombo(I,n);
    G := flatten entries gens (I:m);
    d := 1 + max flatten for i in G list flatten degree i;
    J = J + m^d
    )

end--

TEST ///
///

beginDocumentation()
load (currentFileDirectory | "LocalRings/doc.m2")

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

restart
needsPackage"CoreIdeal"
needsPackage"RandomIdeals"
needsPackage"randomIdeal"
debug CoreIdeal
R = QQ[x,y]--_{0}..x_{2+random 5}]
m = ideal gens R
n = dim R -- analytic spread of monomial ideals containing power of the 

I = ideal"x3,y3"
I = ideal"x2,y4,xy3"
J = randLocal(I,n)
time K = mono(J)
time K' = monoG(J)
assert(K === K')


I = ideal"x2,xy,y2"
J = randomCombo(I,n)
res (R^1/J) -- always 1,2,1 !!
time K = mono(J)
time K' = monoG(J)
assert(K === K')


I = randomMonomialIdeal(apply(2+random 3, i->2+random 8), R)
J = rand(I,n)
time K = mono(J)
time K' = monoG(J)
assert(K === K')



--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

restart -- Let's make a semi-random inhomogeneous ideal
needsPackage"LocalRings"
needsPackage"RandomIdeals"
R = ZZ/101[x,y]
m = ideal gens R
n = 2 -- number of 
N = 4 -- maximum power-2
k = 2 -- how many monomials of each power per generator
I = ideal((for i from 1 to n list random(R^1,R^{k:-2-random N}))//sum)
isHomogeneous I
decompose I

G = flatten entries gens (I:m)
d = 1 + max flatten for i in G list flatten degree i
J = I + m^d

RP = localRing(R, m)
K = ideal mingens J
decompose K
