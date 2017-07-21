cd LPPIdeals
M2
loadPackage("LexIdeals", Reload=>true)
R=ZZ/101[x,y,a,b,c,d,e,f]
I=ideal(x^6,y^6,x^2*a^4+y^2*b^4+x*y*(a^2*c^2+b^2*d^2+a*b*(c*e+d*f)))
minDegRegularSeq(I, UseHeuristics=>true)
R=ZZ/101[x,y,a,b,c]
I=ideal(x,y)
J=ideal(a,b,y)
K=I+J
L=I^3+J^2
LPPK = LPP(K)
hilbertFunct(K)==hilbertFunct(LPPK)
LPPL = LPP(L, UseHeuristics=>true)
hilbertFunct(L)==hilbertFunct(LPPL)
{betti res L, betti res LPPL, betti res lexIdeal L}
