load "FastCodim.m2"
R=ZZ/101[x,y,a,b,c,d,e,f]
I=ideal(x^6,y^6,x^2*a^4+y^2*b^4+x*y*(a^2*c^2+b^2*d^2+a*b*(c*e+d*f)))
J=I*I
Jgens = sort flatten entries mingens J
glf1 = random(1, R)
glf2 = random(1, R)
glf3 = random(1, R)
glf4 = random(1, R)
glf5 = random(1, R)
g1 = first Jgens
g2 = randomIdealElement(4, J)
g3 = randomIdealElement(4, J)
g4 = randomIdealElement(4, J)
