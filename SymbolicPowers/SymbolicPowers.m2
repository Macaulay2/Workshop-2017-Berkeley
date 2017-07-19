newPackage(
        "SymbolicPowers",
	Version => "1.0", 
	Date => "May 14th, 2017",
	Authors => {{Name => "Eloisa Grifo", 
	Email => "eloisa.grifo@virginia.edu"}},
	Headline => "Calculations involving symbolic powers",
	DebuggingMode => false
        )

export {"symbolicPower", "isSymbPowerContainedinPower", "ContainmentProblem", "bigHeight",
    "frobeniusPower", "symbPowerPrimePosChar", "doSymbolicAndOrdinaryPowersCoincide",
    "symbolicPowerJoin", "joinIdeals", "ContainmentProblemGivenSymbolicPower",
    "symbolicContainmentMonomialCurve", "squarefreeGens", "squarefreeInCodim",
    "symbolicPowerMonomialCurve", "isKonig", "isPacked", "noPackedSub", "noPackedAllSubs",
    "minDegreeSymbPower", "lowerBoundResurgence","symbolicDefect"}


bigHeight = method(TypicalValue => ZZ)
bigHeight(Ideal) := ZZ => I -> (if isPrime(I) then codim(I) else 
    (R := ring I; d := dim R; c := codim I; M := R^1/I; 
	if codim Ext^d(M,R) == d then d else 
	(l := toList (c .. d);
	w := apply(l, i->Ext^i(M,R)); v := apply(w,codim); 
	d-position(reverse(v-l),i->i==0))))


fastPower = method(TypicalValue => Ideal)
fastPower(Ideal,ZZ) := Ideal => (I,n) ->
(J := I;
(for i from 1 to n do J = J*I);
J)



doSymbolicAndOrdinaryPowersCoincide = method(TypicalValue => Boolean)
doSymbolicAndOrdinaryPowersCoincide(Ideal,ZZ) := (P,n) -> (Q := P^n; h := bigHeight(P);
    if bigHeight(Q) > h then false else (
	if h==codim(P) then true else symbolicPower(P,n)==Q))
    


isSymbPowerContainedinPower = method(TypicalValue => Boolean)
isSymbPowerContainedinPower(Ideal,ZZ,ZZ) := Boolean => (I,m,n) -> (h := bigHeight I; 
    if m<n then false else (
	if m>= h*n then true else (
	symb := symbolicPower(I,m); pow := I^n; isSubset(symb,pow))))

ContainmentProblem = method(TypicalValue => ZZ)
ContainmentProblem(Ideal,ZZ) := ZZ => (I,n) -> (m := n;
    while not(isSymbPowerContainedinPower(I,m,n)) do m = m+1;
    m)

lowerBoundResurgence = method(TypicalValue => QQ)
lowerBoundResurgence(Ideal, ZZ) := QQ => (I,m) -> 
max apply(toList(1 .. m),o -> (ContainmentProblem(I,o)-1)/o);


ContainmentProblemGivenSymbolicPower = method(TypicalValue => ZZ)
ContainmentProblemGivenSymbolicPower(Ideal,ZZ) := ZZ => (I,m) -> (h := bigHeight(I); 
    e := (m-m%h)/h; n := lift(e,ZZ);
    while isSymbPowerContainedinPower(I,m,n+1) do n = n+1;
    n)


--Given an ideal I and q=p^e, computes the e-th Frobenius power of I
frobeniusPower = method(TypicalValue => Ideal)
frobeniusPower(Ideal,ZZ) := Ideal => (I,q) -> 
ideal(apply(flatten entries gens I, i -> i^q))



--Given integers a and p, finds the largest power of p such that p^k<=a
powersdivision = method(TypicalValue => ZZ)
powersdivision(ZZ,ZZ,ZZ) := ZZ => (a,p,k) -> (if p^k>a then 1 else 
    1+(powersdivision(a,p,k+1)))
powersdivision(ZZ,ZZ) := ZZ => (a,p) -> powersdivision(a,p,1)

--Computes the symbolic power of a prime ideal in characteristic p
--The method is as follows: to compute $I^{(a)}$, find the largest value k with 
-- $q=p^k \leqslant a$
--$I^{(a)} = (I^{[q]} : I^{a-q+1})$
symbPowerPrimePosChar = method(TypicalValue => Ideal)
symbPowerPrimePosChar(Ideal,ZZ) := Ideal => (I,n) -> (R := ring I; p := char R;
    if not(isPrime(I)) 
    then "Not a prime ideal" else (
	h := codim I;
	if p==0 then "The characteristic must be positive" else
	(e := powersdivision(n,p); q := p^e; c := q-1; d := h*c-n+1; J:= I^d;
	    (frobeniusPower(I,q)):J)))



symbPowerMon = method(TypicalValue => Ideal)
symbPowerMon(Ideal,ZZ) := Ideal => (I,n) -> (
    if not(isMonomialIdeal(I)) then "Not a monomial ideal!" else (
	--If I is square-free, the symbolic powers of I are obtained by 
	--intersecting the powers of its associated primes
    if isSquareFree I then 
    (assP := associatedPrimes(I); 
    intersect apply(assP, i -> i^n))
    else 
    --If I is simply monomial, one can collect the primary components in a decomposition
    --of I and intersect the powers of the *maximal* ones
    (primaryDecI := primaryDecomposition I; intersect apply(primaryDecI, i -> i^n))))


symbPowerPrime = method(TypicalValue => Ideal)
symbPowerPrime(Ideal,ZZ) := Ideal => (I,n) -> (if not(isPrime(I)) 
    then "Not a prime ideal" else (primaryList := primaryDecomposition(I^n); 
	res := select(primaryList,i->(radical(i)==I));
	intersect(res)))
    
symbPowerSat = method(TypicalValue => Ideal)
symbPowerSat(Ideal,ZZ) := Ideal => (I,n) -> (R := ring I; m := ideal vars R; saturate(I^n,m))

--Takes a primary decomposition of I^n, picks the components corresponding to the 
--minimal primes of I and intersects them
symbPowerSlow = method(TypicalValue => Ideal)
symbPowerSlow(Ideal,ZZ) := Ideal => (I,n) -> (assI := associatedPrimes(I);
    decomp := primaryDecomposition(I^n);
    comp := select(decomp,a -> isSubset({radical(a)},assI));
    intersect(comp))


symbolicPower = method(TypicalValue => Ideal)
symbolicPower(Ideal,ZZ) := Ideal => (I,n) -> (R := ring I;
    if (codim I == dim R - 1 and isHomogeneous(I) and isPolynomialRing R) then symbPowerSat(I,n) else (
	if isMonomialIdeal I then symbPowerMon(monomialIdeal(I),n) else (
	    if isPrime I then symbPowerPrime(I,n) else 
	    symbPowerSlow(I,n)
	    )))



joinIdeals = method(TypicalValue => Ideal)
joinIdeals(Ideal,Ideal) := Ideal => (I,J) -> (R := ring I; k := coefficientRing(R);
    d := dim(R);
    S := k[vars 1 .. vars (3*d)];
    i := map(S, R, {(vars (d+1))_S .. (vars (2*d))_S});
    j := map(S, R, {(vars (2*d+1))_S .. (vars (3*d))_S});
    use S;
    aux := i -> (vars i)_S - (vars (d+i))_S - (vars (2*d+i))_S;
    extra := apply(toList(1 .. d), aux);
    bigideal := ideal(i(I),j(J), ideal(extra));
    inc := map(S,R,{(vars 1)_S .. (vars d)_S});
    preimage(inc,bigideal)
    );
    
    
symbolicPowerJoin = method(TypicalValue => Ideal);
symbolicPowerJoin(Ideal,ZZ) := Ideal => (p,n) -> (m := ideal(generators ring p);
    joinIdeals(p,m^n))

    
curveIdeal = method(TypicalValue => Ideal)
curveIdeal(List) := Ideal => L -> (d := #L; 
    R := QQ(monoid[vars 1 .. vars d]); S := QQ(monoid[vars 0]); t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); ker f)
curveIdeal(Ring,List) := Ideal => (k,L) -> (d := #L; 
    R := k(monoid[vars 1 .. vars d]); S := k(monoid[vars 0]); t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); ker f)
    
symbolicContainmentMonomialCurve = method(TypicalValue => Boolean);
symbolicContainmentMonomialCurve(List,ZZ,ZZ) := Boolean => (L,m,n) -> (
    I := curveIdeal(L);
    isSymbPowerContainedinPower(I,m,n))
symbolicContainmentMonomialCurve(Ring,List,ZZ,ZZ) := Boolean => (k,L,m,n) -> (
    I := curveIdeal(k,L);
    isSymbPowerContainedinPower(I,m,n))

symbolicPowerMonomialCurve = method(TypicalValue => Ideal);
symbolicPowerMonomialCurve(List,ZZ) := Ideal => (L,m) -> (
    I := curveIdeal(L); symbolicPower(I,m))
symbolicPowerMonomialCurve(Ring,List,ZZ) := Ideal => (k,L,m) -> (
    I := curveIdeal(k,L); symbolicPower(I,m))

-----------------------------------------------------------
-----------------------------------------------------------
--Packing Problem
-----------------------------------------------------------
-----------------------------------------------------------

--Given a monomial ideal, finds a minimal generating set, 
--and then returns the exponents of the monomials in that set
--Given a monomial, returns the exponents
exponentsMonomialGens = method(TypicalValue => List)
exponentsMonomialGens(RingElement) := List => r -> (
    R := ring r;
    k := coefficientRing R;
    d := dim R;
    deg := table(d,d,(i,j) -> if i==j then 1 else 0);
    S := k[toSequence flatten entries vars R,Degrees=>deg];
    f := map(S,R,flatten entries vars S);
    degree(f(r)))
exponentsMonomialGens(Ideal) := List => I -> (
    R := ring I;
    k := coefficientRing R;
    d := dim R;
    deg := table(d,d,(i,j) -> if i==j then 1 else 0);
    S := k[toSequence flatten entries vars R,Degrees=>deg];
    f := map(S,R,flatten entries vars S);
    m := flatten entries(mingens f(I));
    delete({},apply(m,degree)))

squarefreeGensList = method()
squarefreeGensList(Ideal) := List => I ->(
    w := exponentsMonomialGens(I);
    select(w,i -> all(i,o -> o<2)))


squarefreeGens = method()
squarefreeGens(Ideal) := List => I ->(
    w := exponentsMonomialGens(I);
    v := select(w,i -> all(i,o -> o<2));
    R := ring I;
    l := flatten entries vars R;
    apply(v,o->product(apply(toList pairs(o),(i,j)->(l_i)^j))))



--Finds squarefree monomials generating I^c, where c=codim I
squarefreeInCodim = method()
squarefreeInCodim(Ideal) := List => I -> (c := codim I;
    J := I^c;
    squarefreeGens(J))


isKonig = method(TypicalValue => Boolean)
isKonig(Ideal) := Boolean => I -> (R := ring I;
    if I == ideal 1_R then true else (
	if I == ideal(0_R) then true else (
	    c := codim I; J := I^c;
	    not(squarefreeGens(J)=={}))))



replaceVarsBy1 = method(TypicalValue => Ideal)
replaceVarsBy1(Ideal,List) := Ideal => (I,L) -> (w := flatten entries vars ring I;
    v := fold((i,o) -> replace(o,1,i),w,L);
    promote(substitute(I,matrix{v}),ring I))

replaceVarsBy0 = method(TypicalValue => Ideal)
replaceVarsBy0(Ideal,List) := Ideal => (I,L) -> (w := flatten entries vars ring I;
    v := fold((i,o) -> replace(o,0,i),w,L);
    promote(substitute(I,matrix{v}),ring I))
    

isPacked = method(TypicalValue => Boolean)
isPacked(Ideal) := Boolean => I -> (d := # flatten entries vars ring I; 
    s := subsets(d);
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    all(w,x -> isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1))))

noPackedSub = method(TypicalValue => List)
noPackedSub(Ideal) := List => I -> (if not(isKonig(I)) then "The ideal itself is not Konig!" else (
    var := flatten entries vars ring I; d := # var;
    s := delete({},subsets(d));
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    firstFailure := select(1,w,x -> not(isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1))));
    firstFailure = flatten firstFailure;
    varsReplacedBy0 := firstFailure_0;
    varsReplacedBy0 = var_(varsReplacedBy0);
    varsReplacedBy1 := firstFailure_1;
    varsReplacedBy1 = var_(varsReplacedBy1);
    varsReplacedBy0 = apply(apply(varsReplacedBy0,toString),i -> concatenate(i,"=>0"));
    varsReplacedBy1 = apply(apply(varsReplacedBy1,toString),i -> concatenate(i,"=>1"));
    varsReplacedBy0 | varsReplacedBy1))


noPackedAllSubs = method(TypicalValue => List)
noPackedAllSubs(Ideal) := List => I -> (var := flatten entries vars ring I; d := # var;
    s := delete({},subsets(d));
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    allFailures := select(w,x -> not(isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1))));
    allSubs := apply(allFailures, 
	o -> apply(var_(o_0),i->concatenate(toString i,"=>0")) | apply(var_(o_1),i->concatenate(toString i,"=>1")));
    if allSubs == {} then "Only I is not Konig -- all proper substitutions are Konig." else
    allSubs)
    
minDegreeSymbPower = method(TypicalValue => ZZ)
minDegreeSymbPower(Ideal,ZZ) := ZZ => (I,n) -> min flatten degrees symbolicPower(I,n)


isMonomial = method()
isMonomial(RingElement) := r -> (terms(r) == {r})
isMonomial(MonomialIdeal) := I -> true
isMonomial(Ideal) := I -> all(flatten entries mingens I,a -> isMonomial(a))

---------------------------------
---Symbolic Defect
---------------------------------
symbolicDefect = method(TypicalValue => ZZ)
symbolicDefect(Ideal,ZZ) := (I,n) -> (
    R := ring I;
    
    Y := fastPower(I,n);
     
     S := R/Y;
      
      F := map(S,R);
      
      X := symbolicPower(I,n);
      
      # flatten entries mingens F(X)
      )





-----------------------------------------------------------
-----------------------------------------------------------
--Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

document { 
  Key => SymbolicPowers,
  Headline => "A package for computing symbolic powers of ideals",
   
   "This is an experimental version of the package. If you find any typos or errors, please let me know. The package was designed to compute symbolic powers of unmixed ideals in a polynomial ring. It might misbehave in other settings.", 

   SUBSECTION "A quick introduction to this package",
   UL {
    TO "Computing symbolic powers of an ideal",
    TO "Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"
    },
    
 
  SUBSECTION "Other examples which illustrate this package",
  UL {
    TO "The Containment Problem",
    TO "Sullivant's algorithm for primes in a polynomial ring",
    TO "Monomial Curves"
  },

  SUBSECTION "The Packing Problem",
  UL {
    TO "The Packing Problem"
  },
}  



doc ///
     Key
     	  "A quick introduction to this package"
     Headline
     	  How to use this package
     Description
     	  Text
	       Here is a list of some examples which illustrate various parts of this package.
	       
	       {\bf First examples which show how to use this package}
    	       
	       $\bullet$ @TO"Computing symbolic powers of an ideal"@
	       
	       $\bullet$ @TO"Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"@
    	       
 
               {\bf Other examples which illustrate this package}

               $\bullet$ @TO"The Containment Problem"@
	       
	       $\bullet$ @TO"Sullivant's algorithm for primes in a polynomial ring"@
	       
	       $\bullet$ @TO"Monomial curves"@
    	       	     
	       {\bf The Packing Problem}
	       
	       $\bullet$ @TO"The Packing Problem"@
	       
 	  	  
///

doc ///
     Key
     	  "Computing symbolic powers of an ideal"
     Description
     	 Text
	      Given an ideal, symbolicPower computes a given symbolic power.  
	 Example     
	      B = QQ[x,y,z];
	      I = ideal(x*(y^3-z^3),y*(z^3-y^3),z*(x^3-y^3));
	      J = symbolicPower(I,3)
     Description
         Text
              Various algorithms are used, in the following order:     
	      
	      1. If $I$ is a homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I$; 
	      
	      2. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$'
	      
	      3. If $I$ is monomial ideal, but not squarefree, takes an irredundant primary decomposition of $I$ and intersects the powers of those ideals;
	      
	      4. If $I$ is prime, computes a primary decomposition of $I^n$ and intersects the components with radical $I$.
	      
	      5. If all else fails, compares the radicals of a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the unmixed components.
///



doc ///
     Key
     	  "Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"
     Description
     	 Text
	      Given a prime ideal P in a regular ring of positive characteristic, symbPowerPrimePosChar computes its symbolic powers. Unfortunately, this algorithm is slower than others.  
	      
	 Example     
	      R = ZZ/7[x,y,z]
	      P = ker map(ZZ/7[t],R,{t^3,t^4,t^5})
	      J = symbPowerPrimePosChar(P,2)
	 Text
	      The symbolic powers of P do not coincide with its powers.
	 Example     
	      J == P^2
	 Text
	      We can also test it a bit faster, without computing the symbolic powers of P:
	 Example
	      doSymbolicAndOrdinaryPowersCoincide(P,2)

///



doc ///
     Key
     	  "The Containment Problem"
     Description
     	 Text
	      Given an ideal I, we can determine if $I^{(m)} \subseteq I^n$. For example, here is an ideal that fails the containment $I^{(3)} \subseteq I^2$:
	 Example     
	      B = ZZ/101[x,y,z];
	      I = ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	      isSymbPowerContainedinPower(I,3,2)
     	 Text
	      We can also determine the smallest symbolic power contained in a given power.
     	 Text
	      In our example, $I^{(4)}$ is the smallest symbolic power contained in $I^2$:
	 Example
	      ContainmentProblem(I,2)
     	 Text
	      We can ask the same question backwards: what is the largest power of I that contains $I^{(4)}$?
	 Example
	      ContainmentProblemGivenSymbolicPower(I,4)     
///



doc ///
     Key
     	  "Sullivant's algorithm for primes in a polynomial ring"
     Description
     	 Text
	      Given ideals I and J in a polynomial ring, we compute their join I*J:  
	 Example     
	      S = QQ[x,y,z];
	      I = ideal(x^3,x^2*y^2,x*z^3,y^4,y^2*z);
	      J = joinIdeals(I,I)
     	 Text
	      Following Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142, we can compute symbolic powers of prime ideals using join:
	 Example     
	      A = QQ[x,y,z];
	      symbolicPowerJoin(ideal(x,y),2)  
       	 Example
	      f = map(QQ[t],A,{t^3,t^4,t^5})
	      P = ker f;
	      symbolicPowerJoin(P,2)
///



doc ///
     Key
     	  "Monomial Curves"
     Description
     	 Text
	      To test containments of symbolic and ordinary powers of ideals defining monomial curves, we can skip the step where we define the ideals.
     	 Text
	      For example, if I is the ideal defining the monomial curve defined by $t^3, t^4, t^5$ over $\mathbb{Z}/101$, we can ask whether $I^{(3)} \subseteq I^2$:
	 Example     
	      symbolicContainmentMonomialCurve(ZZ/101,{3,4,5},3,2)
     	 Text
	      Or we simply ask for the symbolic powers of these ideals. For example, here is the third of the same ideal:
	 Example     
	      symbolicPowerMonomialCurve(ZZ/101,{3,4,5},3)
///



doc ///
     Key
     	  "The Packing Problem"
     Description
     	 Text
	      Given a square-free monomial ideal I of codimension c, I is Konig if it contains a regular sequence of monomials of length c.
     	 
	      We can test if a given ideal is Konig:
	 Example     
	      R = QQ[x,y,z]
	      I = ideal(x*y,z*y,x*z)
	      isKonig(I)
     	 Text
	      I is said to have the packing property if any ideal obtained from I by setting any number of variables equal to 0 is Konig.
	 Example     
	      isPacked(I)
     	 Text
	      Given an ideal that is not packed, we can determine which variable substitutions lead to ideals that are not Konig.
	 Example     
	      noPackedAllSubs(I)
     	 Text
	      We can obtained just one substitution leading to an ideal that is not Konig, or all such substitutions:
	 Example     
	      R = QQ[a,b,c,d,A,B,C,D]
	      J = ideal"ABCD,cdAB,abcD,bcABD,abcBD,abcdA,abcAD,abdAC,acdBC,acBCD,abcdC,bcdAC,bcACD,bcdAD,acdBD,adBCD,acABD,bdABC,adABC"
	      isPacked(J)
	      noPackedSub(J)
     	 Text
	      These can easily be tested:
	 Example     
	      L = substitute(J,matrix{{1,0,c,d,A,1,C,D}})
	      isKonig(L)

///




doc ///
   Key
       bigHeight
       (bigHeight, Ideal)
   Headline
       Big height of an ideal: the largest height of an associated prime
   Usage
       bigHeight(I)
   Inputs
        I:Ideal
   Outputs
       :ZZ
           the largest height of an associated prime of I
   Description
       Text  
           The algorithm is based on the following result by Eisenbud-Huneke-Vasconcelos, 
	   in their 1993 Inventiones Mathematicae paper:
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all d
	   $\bullet$ If P is an associated prime of M of codimension d := codim P > codim M, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in P
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension d.
       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   bigHeight(J)
   SeeAlso
       codim
///

doc ///
   Key
       isSymbPowerContainedinPower
       (isSymbPowerContainedinPower, Ideal, ZZ, ZZ)
   Headline
       Tests if the m-th symbolic power an ideal is contained the n-th in a power
   Usage
       isSymbPowerContainedinPower(I,m,n)
   Inputs
        I:Ideal
    	m:ZZ
    	n:ZZ
   Outputs
       :Boolean
           whether the m-th symbolic power of 'I' is contained in the n-th power
   Description
       Example
           R = QQ[x,y,z]
     	   J = ideal(x,y)
    	   isSymbPowerContainedinPower(J,3,2)
   SeeAlso
       ContainmentProblem
///


doc ///
   Key
       ContainmentProblem
       (ContainmentProblem, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the order of the smallest symbolic power of I contained in I^n.
   Usage
       ContainmentProblem(I,n)
   Inputs
	I:Ideal
	n:ZZ
   Outputs
       :ZZ
           the minimum value m such that the m-th symbolic power of I is contained in I^n
   Description
       Example
	   B = QQ[x,y,z];
	   f = map(QQ[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   m = ContainmentProblem(I,2)
   SeeAlso
       isSymbPowerContainedinPower
       ContainmentProblemGivenSymbolicPower
///


doc ///
   Key
       ContainmentProblemGivenSymbolicPower
       (ContainmentProblemGivenSymbolicPower, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the order of the largest power of I containing in I^{(n)}.
   Usage
       ContainmentProblemGivenSymbolicPower(I,m)
   Inputs
	I:Ideal
	m:ZZ
   Outputs
       :ZZ
           the largest value n such that I^n contains the m-th symbolic power of I.
   Description
       Example
	   B = QQ[x,y,z];
	   f = map(QQ[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   ContainmentProblemGivenSymbolicPower(I,3)
   SeeAlso
       ContainmentProblem
///

doc ///
   Key
       frobeniusPower
       (frobeniusPower, Ideal, ZZ)
   Headline
       Given an ideal I in characteristic p and q=p^e, returns the q-th Frobenius power of I.
   Usage
       frobeniusPower(I,q)
   Inputs
	I:Ideal
	q:ZZ
   Outputs
       :Ideal
           the q-th Frobenius power of I
   Description
       Example
	   B = ZZ/7[x,y,z];
	   f = map(ZZ/7[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   frobeniusPower(I,7)
///

doc ///
   Key
       symbPowerPrimePosChar
       (symbPowerPrimePosChar, Ideal, ZZ)
   Headline
       Given an ideal I in a polynomial ring over a field of positive characteristic, and an integer n, returns the n-th symbolic power of I contained.
   Usage
       	symbPowerPrimePosChar(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Ideal
           the n-th symbolic power of I
   Description
       Text  
           To compute $I^{(a)}$, find the largest value k with $q = p^k \leq a$. Then $I^{(a)} = (I^{[q]} : I^{a-q+1})$.
       Example 
           B = ZZ/7[x,y,z];
	   f = map(ZZ/7[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   symbPowerPrimePosChar(I,2)
   SeeAlso
       symbolicPower
///



doc ///
   Key
       symbolicPower
       (symbolicPower, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the n-th symbolic power of I.
   Description
       Text
              Various algorithms are used, in the following order:     
	      
	      1. If $I$ is a homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I$; 
	      
	      2. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$'
	      
	      3. If $I$ is monomial ideal, but not squarefree, takes a primary decomposition of $I$, picks the maximal elements in it, and intersects their powers;
	      
	      4. If $I$ is prime, computes a primary decomposition of $I^n$ and intersects the components with radical $I$.
	      
	      5. If all else fails, compares the radicals of a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the unmixed components.
   Usage
       	symbolicPower(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Ideal
           the n-th symbolic power of I
   Description
       Example
              B = QQ[x,y,z];
	      f = map(QQ[t],B,{t^3,t^4,t^5})
	      I = ker f;
	      symbolicPower(I,2)
   SeeAlso
      symbPowerPrimePosChar
///



doc ///
   Key
       doSymbolicAndOrdinaryPowersCoincide
       (doSymbolicAndOrdinaryPowersCoincide, Ideal, ZZ)
   Headline
       Given a radical ideal I and an integer n, returns true iff $I^n=I^{(n)}$.
   Usage
       	doSymbolicAndOrdinaryPowersCoincide(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Boolean
           the truth value of $I^n==I^{(n)}$
   Description
       Text
              Circumvents computing the symbolic powers in most cases, by first testing the bigheigh of $I^n$
       Example
              B = QQ[x,y,z];
	      f = map(QQ[t],B,{t^3,t^4,t^5})
	      I = ker f;
	      doSymbolicAndOrdinaryPowersCoincide(I,2)
   SeeAlso
      isSymbPowerContainedinPower
///



doc ///
   Key
       joinIdeals
       (joinIdeals,Ideal,Ideal)
   Headline
       Computes the join of the given ideals
   Usage
       joinIdeals(Ideal,Ideal)
   Inputs
        I:Ideal
	J:Ideal
   Outputs
       :Ideal
 --          the join of I and J
   Description
       Text    
           See Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142, for a definition.
       Example
           S = QQ[x,y,z];
	   I = ideal(x^3,x^2*y^2,x*z^3,y^4,y^2*z);
	   J = joinIdeals(I,I)
///


doc ///
     Key 
         symbolicPowerJoin
	 (symbolicPowerJoin,Ideal,ZZ)
     Headline 
         Symbolic powers of prime ideals using Sullivant's algorithm.
     Usage 
         symbolicPowerJoin(P,n)
     Inputs 
	  P:Ideal
	  n:ZZ
     Outputs
          :Ideal
--  the n-th symbolic power of P
     Description	  
       Text
	   Computes the n-th symbolic power of the prime ideal P, using join of ideals.
	   
	   This is the algorithm in Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142.
       Example 
	   A = QQ[x,y,z]
	   symbolicPowerJoin(ideal(x,y),2) 
     SeeAlso 
	  joinIdeals
/// 




doc ///
     Key 
         symbolicContainmentMonomialCurve
	 (symbolicContainmentMonomialCurve,List,ZZ,ZZ)
	 (symbolicContainmentMonomialCurve,Ring,List,ZZ,ZZ)
     Headline 
         Tests the containment of symbolic in ordinary powers of ideals for monomial curves.
     Usage 
         symbolicContainmentMonomialCurve(L,m,n)
	 symbolicContainmentMonomialCurve(k,L,m,n)
     Inputs 
     	  k:Ring
	  L:List
	  m:ZZ
	  n:ZZ
     Outputs
          :Boolean
     Description	  
       Text
	   Tests whether $I^{(m)} \subseteq I^n$, where $I$ is the defining ideal for the monomial curve defined by $t^{a_1}, \ldots, t^{a_n}$. If no field is provided, the ideal is defined over $\mathbb{Q}$.
       Example 
	   symbolicContainmentMonomialCurve({3,4,5},3,2) 
     SeeAlso 
	  isSymbPowerContainedinPower
	  symbolicPowerMonomialCurve
/// 



doc ///
     Key 
         symbolicPowerMonomialCurve
	 (symbolicPowerMonomialCurve,List,ZZ)
	 (symbolicPowerMonomialCurve,Ring,List,ZZ)
     Headline 
         Computes the symbolic powers of ideals defining monomial curves.
     Usage 
         symbolicPowerMonomialCurve(L,m)
	 symbolicPowerMonomialCurve(k,L,m)
     Inputs 
     	  k:Ring
	  L:List
	  m:ZZ
     Outputs
          :Ideal
     Description	  
       Text
	   Finds the m-th symbolic power of I, where I is the defining ideal for the monomial curve defined by $t^{a_1}, \ldots, t^{a_n}$. If no field is provided, the ideal is defined over $\mathbb{Q}$.
       Example 
	   symbolicPowerMonomialCurve({3,4,5},3) 
     SeeAlso 
	  ContainmentProblem
/// 




doc ///
     Key 
         squarefreeGens
	 (squarefreeGens,Ideal)
     Headline 
         Returns all square-free monomials in a minimal generating set of the given ideal.
     Usage 
         squarefreeGens(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal I, returns all square-free monomials in a minimal generating set of I.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x^2)
	   squarefreeGens(I) 
     SeeAlso 
	  squarefreeInCodim
/// 

doc ///
     Key 
         squarefreeInCodim
	 (squarefreeInCodim,Ideal)
     Headline 
         Finds square-fee monomials in I^c, where c is the codimension of the given ideal.
     Usage 
         squarefreeInCodim(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal I, returns all square-free monomials in a minimal generating set of I^c.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x*z)
	   squarefreeInCodim(I) 
     SeeAlso 
	  squarefreeGens
///



doc ///
     Key 
         isKonig
	 (isKonig,Ideal)
     Headline 
         Determines if a given square-free ideal is Konig.
     Usage 
         isKonig(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal I, determines if the ideal is Konig.
       Text
	   A square-free monomial ideal I of codimension c is Konig if it contains a regular sequence of monomials of length c.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x*z)
	   isKonig(I) 
     SeeAlso 
	  squarefreeGens
///

doc ///
     Key 
         isPacked
	 (isPacked,Ideal)
     Headline 
         Determines if a given square-free ideal is packed.
     Usage 
         isPacked(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal I, determines if the ideal is Konig.
       Text
	   A square-free monomial ideal I of codimension c is packed if every ideal obtained from it by replacing any number of variables by 1 or 0 is Konig.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x*z)
	   isPacked(I) 
     SeeAlso 
	  squarefreeGens
///


doc ///
     Key 
         noPackedSub
	 (noPackedSub,Ideal)
     Headline 
         Finds a substitution of variables by 1 and/or 0 for which I is not Konig.
     Usage 
         noPackedSub(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given an ideal that is not packed, returns a substitution of variables by 0 and/or 1 that produces an ideal that is not Konig.
       Text
	   Determines only one such substitutions, even though others may exist.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x*z)
	   noPackedSub(I) 
     SeeAlso 
	  isPacked	  
///
	  

doc ///
     Key 
         noPackedAllSubs
	 (noPackedAllSubs,Ideal)
     Headline 
         Finds all substitutions of variables by 1 and/or 0 for which I is not Konig.
     Usage 
         noPackedAllSubs(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given an ideal that is not packed, returns a list with all substitution of variables by 0 and/or 1 that produces an ideal that is not Konig.
       Example 
	   R = QQ[x,y,z]
	   I = ideal(x*y,y*z,x*z)
	   noPackedAllSubs(I) 
     SeeAlso 
	  noPackedSub
	  isPacked	  
///

doc ///
     Key 
         minDegreeSymbPower
	 (minDegreeSymbPower,Ideal,ZZ)
     Headline 
         Returns the minimal degree of a given symbolic power of an ideal.
     Usage 
         minDegreeSymbPower(Ideal,ZZ)
     Inputs 
     	  I:Ideal
	  n:ZZ
     Outputs
          :ZZ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, returns the minimal degree of an element in $I^{(n)}$.
       Example 
	   T = QQ[x,y,z]
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z")
	   minDegreeSymbPower(I,2)

///

doc ///
     Key 
         lowerBoundResurgence
	 (lowerBoundResurgence,Ideal,ZZ)
     Headline 
         Computes a lower bound for the resurgence of a given ideal
     Usage 
         lowerBoundResurgence(Ideal,ZZ)
     Inputs 
     	  I:Ideal
	  n:ZZ
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, finds the maximum of the quotiens m/k that fail $I^{(m)} \subseteq I^k$ with $k \geq n$.
       Example 
	   T = QQ[x,y,z]
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z")
	   lowerBoundResurgence(I,5)

///





TEST ///
   S = QQ[x,y,z];
   I = ideal(x,y,z);
   assert(isSymbPowerContainedinPower(I,2,2) == true)
///

end
