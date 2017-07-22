newPackage(
	"AbsFac",
	Version => "0.2", 
    	Date => "Jul 19, 2017",
    	Authors => {{Name => "Martin Helmer", 
		  Email => "martin.helmer2@gmail.com", 
		  HomePage => "https://math.berkeley.edu/~mhelmer/"}
	      },
    	Headline => "Abs Fac",
    	DebuggingMode => true,
	Reload => true
    	);
export{"absIrrTestRag","absIrrTestBCG","absFactor"
    }
needsPackage "Polyhedra";

absFactor=method(TypicalValue=>List);
absFactor RingElement:=F->(
    --TODO: this method will convert eg.m2 to a function....
    return 0;
    );
--Method to test Absolute Irreducibility in two variables, Ragot, see page 7 BCG
absIrrTestRag=method(TypicalValue=>Boolean);
absIrrTestRag RingElement:=f->(
    print "This method may not work (not tested)";
    R:=ring(f);
    gcdlist:={};
    S:=ZZ/7[gens(R)];
    pis:={};
    tiL:={};
    df:=flatten entries jacobian ideal f;
    df1:=first df;
    df2:=last df;
    ---list of primes
    for i from 7 to 101 do (
    	if isPrime i then pis=append(pis,i);
    	);
    --print pis;
    for p in pis do(
	<<"p= "<<p<<endl;
	S=ZZ/p[gens(R)];
	time(
	    tiL={};
	if #factor(sub(f,S))==1 then(
    	    for a from 1 to p do (
    	    	for b from 1 to p do(
		    Fab:=sub(sub(f,S),{S_0=>a,S_1=>b});
		    if Fab==0_S then(	
			if sub(sub(df1,S),{S_0=>a,S_1=>b})!=0 or sub(sub(df2,S),{S_0=>a,S_1=>b})!=0  then(
			    --condition C is satisfied
		    	    <<"p= "<<p<<" ,a= "<<a<<" ,b= "<<b<<endl;
		    	    --break;
		    	    return true;
		    	    );
		    	);
	    	    );
	    	);
	    <<"for p= "<<p<<", time for poly+ gcd= "<<sum(tiL)<<endl;
	    )
    	else(<<"bad reduction forp= "<<p<<endl;);
	);
    	);
    return gcdlist;
    );
--Method to test Absolute Irreducibility in two variables
--this method is faster (a little) if the input is actually abs irreducible
--but takes a very long time if not
--perhaps the top prime should be made much smaller and if it fails it should
--fallback to Rag. method above
	--Condition C from BCG paper is very slow in M2
			--in particular the newton polytope function
			--takes a very long time
			--I think the orgin of this problem is the Fourier-Moutzkin 
			--package
			--Use Ragot "Fact" instead, see page 7 BCG
			--for the other implementation 
absIrrTestBCG=method(TypicalValue=>Boolean);
absIrrTestBCG RingElement:=f->(
    R:=ring(f);
    gcdlist:={};
    S:=ZZ/7[gens(R)];
    pis:={};
    tiL:={};
    df:=flatten entries jacobian ideal f;
    df1:=first df;
    df2:=last df;
    ---list of primes
    for i from 7 to 101 do (
    	if isPrime i then pis=append(pis,i);
    	);
    --print pis;
    for p in pis do(
	<<"p= "<<p<<endl;
	S=ZZ/p[gens(R)];
	    --tiL={};
	if #factor(sub(f,S))==1 then(
    	    for a from 1 to p do (
    	    	for b from 1 to p do(
	    	    F1:=sub(sub(f,S),{S_0=>S_0+a,S_1=>S_1+b});
		    if degree(F1)==degree(f) then(	
		        t1:=timing (P:=newtonPolytope F1;);
     	    	    	vert:=vertices P;
		    	vertgcd:=gcd(flatten entries flatten vert);
		    	gcdlist=append(gcdlist,vertgcd);
	    	    	if vertgcd==1 then(
			    --condition C is satisfied
		    	    <<"p= "<<p<<" ,a= "<<a<<" ,b= "<<b<<endl;
		    	    print vert;
		    	    --break;
		    	    return true;
		    	    );
		    tiL=append(tiL, first t1);
		    	);
	    	    );
	    	);
	    <<"for p= "<<p<<", time for poly+ gcd= "<<sum(tiL)<<endl;
	    )
    	else(<<"bad reduction forp= "<<p<<endl;);
	);
    return gcdlist;
    );
TEST ///
{*  
    restart
    needsPackage "AbsFac"
    not abs irr ex
*}

setRandomSeed 12345
-- First we construct an example
A = ZZ[x,y,u]
R = ZZ[y,x,z,MonomialOrder=>Lex]
phi = map(R,A,{x,y,1})
B = ZZ[y,x, MonomialOrder=>Lex]
C = ZZ[y]
deg = 4
zdeg = 3
use R
G1 = y^deg + sum for i from 0 to zdeg-1 list phi random(deg-1,A) * z^i
G2 = z^zdeg + sum for i from 0 to zdeg-1 list (random ZZ) * z^i
F = sub(resultant(G1,G2,z), B)
factor F
--
time absIrrTestRag F
--since this is not abs irr. BCG will be very slow
time absIrrTestBCG F

///

TEST ///
{*  
    restart
    needsPackage "AbsFac"
    --abs irr ex
*}

setRandomSeed 12345
R=ZZ[x,y]
f=random(12,R)+random(2,R)+23
--BCG finds it quickly, rag not at all (this may be an implementation bug). 
time absIrrTestRag f
time absIrrTestBCG f

///