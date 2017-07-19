load "LPPFromIdeal.m2"
R=ZZ/101[x_1..x_6]
I=minors(2,genericSymmetricMatrix(R,x_1,3))
print(I)
print(hilbertFunct I == hilbertFunct LPPFromIdeal(I))
print(isLPPNonFull LPPFromIdeal(I))
