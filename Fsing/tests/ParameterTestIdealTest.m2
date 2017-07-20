
--load "c:/New Berkeley 2017/Workshop-2017-Berkeley/Fsing/TestIdeals.m2"
TEST /// 

p=2;
R=ZZ/p[x_1..x_5]; 
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);

time assert(isCohenMacaulay(R/I) == true);

Omega=canonicalIdeal(R/I);
time assert(Omega==ideal(x_1, x_4, x_5));
u=finduOfIdeal(I,Omega);
time assert(u== x_1^3*x_2*x_3+x_1^3*x_2*x_4+x_1^2*x_3*x_4*x_5+x_1*x_2*x_3*x_4*x_5+x_1*x_2*x_4^2*x_5+x_2^2*x_4^2*x_5+x_3*x_4^2*x_5^2+x_4^3*x_5^2); 
time assert(testModule(R,I)==ideal(x_3+x_4, x_2, x_1, x_4*x_5));
time assert(isFrational(R/I)==false);



S=ZZ/101[a,b,x,y,u,v, MonomialOrder=>ProductOrder{2,4}];
time assert(isCohenMacaulay(S) == true);
J=ideal(x-a^4, y-a^3*b, u-a*b^3, v-b^4);
G=gens gb J;
K=selectInSubring(1,G);
time assert(isCohenMacaulay(S/K) == false);

pp=11;
R=ZZ/pp[x_1..x_3];
I=ideal(x_1^3+x_2^3+x_3^3);
time assert(testModule(R/I)==ideal(x_1, x_2, x_3));
time assert(isFrational(R/I)==false);


///