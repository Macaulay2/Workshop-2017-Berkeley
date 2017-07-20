needsPackage"LocalRings"
needsPackage"RandomIdeals"

multiHomog = I -> (
    R = ring I;
    N = numgens R;
    S = (coefficientRing R)(monoid [gens R, T_{0}..T_{N-1}]);
    G = sub(gens I, S);
    for i from 0 to N-1 do
        G = homogenize(G, T_{i}, 
            apply(N, j -> if i==j then 1 else 0) | 
            apply(N, j -> if i==j then 1 else 0));
    ideal G
    )

restart
R = ZZ/101[x,y,z]
I = ideal"z3+y+1"
multiHomog(I)


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




















