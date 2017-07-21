Examples:

R = ZZ/31013[x_1 .. x_6]  - polynomial ring with 6 variables

f1 = 2*x_2^2+3*x_3^2+x_5^2
f2 =  x_1^2-x_4^2+x_4*x_5
f3 = x_1*x_5 - x_2*x_4 + 2*x_6^2
f4 = x_6^2-x_1*x_5

--In case we need two more: f5 = x_2*x_3+5*x_1*x_4+x_5^2
                            f6 = x_3^2+3*x_6*x_5

isRegularSequence {f1,f2,f3,f4} -- true
F = ideal(f1,f2,f3,f4)
g = random(3,R)
I = F^2 + ideal(g^2)
minDegRegularSeq(I)  -- {4,4,4,4,6}
L = LPPFromIdeal(I)
hilbertFunct(I)
hilbertFunct(L)
{betti res I, betti res L}

----------
