newPackage(
	"SimpleFGLM",
	Version => "0.2", 
    	Date => "Jul 19, 2017",
    	Authors => {{Name => "Martin Helmer", 
		  Email => "martin.helmer2@gmail.com", 
		  HomePage => "https://math.berkeley.edu/~mhelmer/"}},
    	Headline => "Top level implmentation of FGLM",
    	DebuggingMode => false,
	Reload => true
    	);
export{"fglm"
    }

--------------------------------------------
--
--Reqires a zero dimensional ideal, 
-- i.e. R/I must be a finite dimensional vector space
--rewrites a GB to LEX order
-------------------------------------------
fglm=method(TypicalValue=>Ideal);
fglm Ideal:=I->(
    I=ideal groebnerBasis I;
    R:=ring I;
    --W:=R/I;
    if dim(I)>0 then( error"needs zero dim"; return 0;);
    B:=flatten entries basis (R/I);
    gbLex:={};
    NlexB1:={1_R};
    NlexB2:={1_R};
    xs:=reverse gens(R);
    r:=1_R;
    te:={for b in B list r_b};
    coefs:={};
    tempNlex:={};
    m1:=0;
    Tnorm:=0;
    temp2:={};
    timList:={};
    for i from 0 to #xs-1 do(
	r=(xs_i)^0;
	for l from 1 to #B do(
	    r=(r*xs_i)%I;
	    temp2=for b in B list r_b;
	    m1=(matrix te)||matrix{temp2};
	    if rank(m1)==numRows(m1) then(
		NlexB1=append(NlexB1, r);
		NlexB2=append(NlexB2,xs_i^(l));
		te= append(te,temp2);
		)
	    else(
		coefs=flatten entries transpose gens ker transpose m1;
		tempNlex=append(NlexB2,xs_i^l);
		gbLex=append(gbLex,sum(0..#coefs-1,k->tempNlex_k*coefs_k));
		break;
	    );
	);
    );
    S:=coefficientRing(R)[gens(R),MonomialOrder=>Lex];
    Is:=sub(ideal(gbLex),S);
    return Is;
    );


TEST ///
{*  
    restart
    needsPackage "SimpleFGLM"
*}
    R=QQ[x_1..x_3];
    I=ideal(random(3,R),x_1^2-34*x_1*x_2*x_3-34,random(3,R));    
    assert(dim(I)==0);
    time G=fglm I;
    S=coefficientRing(R)[gens(R),MonomialOrder=>Lex];
    time G2=ideal groebnerBasis sub(I,S);
    assert(sub(G,S)==G2)
///

TEST ///
{*  
    restart
    needsPackage "SimpleFGLM"
*}
    R=QQ[x,y,z];
    I=ideal(980*z^2 - 18*y - 201*z + 13, 35*y*z -4*y + 2*z - 1, 10*y^2 - y -12*z + 1, 5*x^2 - 4*y + 2*z - 1);
    Gi=fglm I
    J=ideal(770*z^4 - 4*y - 201*z^2 + 13, 35*y*z^2 -4*y + 12*z - 1, 52*x^2 - 4*y + 2*z - 1);
    Gj=time fglm J
    S=coefficientRing(R)[gens(R),MonomialOrder=>Lex];
    time Gj2=ideal groebnerBasis sub(J,S);
    assert(sub(Gj,S)==Gj2)
///
