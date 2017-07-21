newPackage(
    "PotentialBettiTables",
    Version => "0.1",
    Date => "July 19, 2017",
    Authors => {{
	    Name => "Juliette Bruce", 
	    Email => "juliette.bruce@math.wisc.edu", 
	    HomePage => "http://www.math.wisc.edu/~juliettebruce/"},
	{
	    Name => "Mike Loper",
	    Email => "loper012@umn.edu",
	    HomePage => "http://www.math.umn.edu/~loper012"},
	{
	    Name => "Michael Perlman",
	    Email => "",
	    HomePage => ""}}
    Headline => "computes family of all possible Betti tables of a 0-dimensional grade module",
    DebuggingMode => true
  )

needsPackage "SimpleDoc"
needsPackage "BoijSoederberg";

export {
    "maxBetti",
    "maxBettiReg2Cyclic",
    "makeBettiFromHash",
    "isInCone",
    "possibleCancelations",
    "possibleBettiTables"
    }

maxBetti= method()
---the maximal betti table given a hilbert function and a ring
maxBetti(ZZ,List) := (n,h) -> (
       maxGradedBetti := (i,j)-> h_(j-i)*binomial(n,i);
       maxBettiList := {};
       L := flatten apply(n+1,p->(apply(#h,q->{(p,q), maxGradedBetti(p,p+q)})));
       new HashTable from L
       )
     
maxBettiReg2Cyclic= method()
---the maximal betti table of a cyclic zero dimensional module with a given hilbert function
maxBettiReg2Cyclic(ZZ,List) := (n,h) -> (
    M := new MutableHashTable from maxBettiReg2(n,h);
    for j from 1 to 2 do 
         (M#(1,j-1)= M#(1,j-1)-M#(0,j);
	  M#(0,j)=0);
    for j from 0 to 1 do
         (if (M#(1,j))==0 then 
	     (for i from 2 to n do
	         (M#(i-1,j+1)=M#(i-1,j+1)-M#(i,j);
		  M#(i,j)=0)));
    for i from 2 to n do
        (if (M#(i,1))==0 and M#(i,0)==0 then
	    (for k from i+1 to n do
	        (M#(k-1,2)=M#(k-1,2)-M#(k,1);
		 M#(k,1)=0)));
    new HashTable from M 
    )	

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

makeBettiFromHash = H ->(
    new BettiTally from apply(keys H, h-> (h_0,{h_0+h_1},h_0+h_1)=> H#h)
    )

fromHashToDiagMatrix = H ->(
    pd := (max(keys H))#0;
    reg := (max(keys H))#1;
    
    M1 := apply(pd+1, p->(apply(min(pd,reg)+1,i->(
		    if isSubset({(p-i,i)},keys H)==true then H#(p-i,i)
		    else 0
		    ))
	    ));
    M2 := reverse apply(reg, q->(apply(min(pd,reg)+1,i->(
		    if isSubset({(pd-i,reg-q+i)},keys H)==true then H#(pd-i,reg-q+i)
		    else 0
		    ))
	    ));
    matrix (M1 | M2)
    )

-- we need to tell it the projective dimension.
fromDiagMatrixToHash = (M,d) ->(
    -- m is equal to min(pd,reg)+1
    m := #flatten entries M^{0};
    n := #flatten entries M_{0};
    reg := n - (d+1);
    H := new MutableHashTable;
    apply(d+1, p->(
	    apply(m,i->(
		if (p-i)>-1 then (H#(p-i,i)=M_(p,i))
		))
	    ));
    apply(reg, q->(apply(m,i->(
			H#(d-i,q+i+1)=M_(d+1+q,i)
			))
		));
    new HashTable from H
    )

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

isStrictlyIncreasing = L->(
     t:=true;
     for i from 0 to #L-2 do t=(t and (L_i<L_(i+1)));
     t)

isInCone = method() 
isInCone BettiTally := B -> (
    t := true;
    B1 := new MutableHashTable from B;
    while min values B1 >= 0 and max values B1 > 0 and t==true do (
	T := new BettiTally from B1;
	L := lowestDegrees T;
	t = isStrictlyIncreasing L;
	if t == true then (
	    C := pureBettiDiagram L;
     	    C := makePureBettiDiagram L;     
     	    ratio := min apply(#L, i->(T#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     	    X = (C,ratio,merge(T,C, (i,j)->i-ratio*j));
	    B1 = new MutableHashTable from X_2;
	    )
	else (
	    t = false
	    )
	);
    t
    )

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

sieveZeroPropogations = H ->(
    pd := (max(keys H))#0;
    reg := (max(keys H))#1;
    t := true;
    
    apply(reg, q->(
	    if t == true then (
		apply(pd,p->(
			if t == false then t = false
			else (
			    if H#(pd-(p+1),q) == 0 and H#(pd-p,q) != 0 then (
				if unique apply(q,i->(H#(pd-(p+1),i)==0))=={true} then (
				    t = false
				    )
				else (
				    t = true
				    )
				)
			    else ( 
				t = true
				)
			    )
			));
		)));
    t
    )

possibleCancelations = method()
possibleCancelations (HashTable) := H ->(
    pd := (max(keys H))#0;
    reg := (max(keys H))#1;
    
    M := entries fromHashToDiagMatrix(H);
    Z := apply(M, i->apply(i,j->0));
    
    -- This first sieves out tables whose alter. sums are not the same.
    X1 := matrix apply(min(pd,reg)+1,i->{(-1)^i});
    C1 := (matrix M)*X1;
    L1 := delete(,apply(drop(toList(Z..M),0),i->(if (matrix i)*X1 == C1 then i)));	    
    
    -- This sieves out the tables whose consecutive sums are not the same.
    l := {1,-1}|apply(min(pd,reg)-1,i->0);
    X2 := apply(min(pd,reg),i->((apply(i,j->0))|drop(l,-i)));
    C2 := (matrix M)*X2;
    L2 := delete(,apply(L1,i->(if (matrix i)*X2 == C2 then i)));
    
    -- This sieves out the tables where zeros do not propogate.
		
    L3 := apply(L2,i->fromDiagMatrixToHash(matrix i,pd));
    
    apply(L3,i->
	
    )
    
possibleBettiTables = method()
possibleBettiTables (HashTable) := H ->(
    delete(,apply(possibleCancelations(H),i-> if isInCone(makeBettiFromHash(i))==true then makeBettiFromHash i))	
    )      
end

--------------------------------------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------------------------------------
beginDocumentation()
doc ///
    Key
    	PotentialBettiTables
    Headline
    	exploring the family of all possible Betti tables of 0-dimensional grade modules
    Description
    	Text
	    This package explores the family of all possible Betti tables of a 0-dimesional graded module with a specified Hilbert function.
    Caveat
        This package is underdevelopment.
///

doc ///
    Key
    	makeBettiFromHash
	(makeBettiFromHash,HashTable)
    Headline
    	turns the HashTable representing a Betti table into a BettiTally
    Usage
    	B = makeBettiFromHash(H)
    Inputs
    	H:HashTable
	    representing a Betti table
    Outputs
    	B:BettiTally
	    from the given HashTable
    Description
    	Text
	    Given a HashTable representing a Betti table this returns a 
	    BettiTally representing the same table
	    
	Example
	    H = new HashTable from {(0,0) => 1, (0,1) => 0, (1,0) => 0, (2,0) => 0, (0,2) => 0, (1,1) => 6, (3,0) => 0, (2,1) => 8, (1,2) => 0, (3,1) => 3, (2,2) => 0, (3,2) => 0};
	    makeBettiFromHash(H) 	
///

doc ///
    Key
    	isInCone
	(isInCone,BettiTally)
    Headline
    	determines whether a given abstract Betti table is in the B-S cone
    Usage
    	t = isInCone(B)
    Inputs
    	B:BettiTally
	    representing an abstract Betti table
    Outputs
    	t:Boolean
	    stating whether the given table is in the B-S cone	    
    Description
    	Text
	    Given an abstract Betti table this returns True or False 
	    depending on whether or not the table lies in the B-S cone.
	    
	Example
	    segreIdeal({1,1})
	    segreIdeal({1,2})  	
///

doc ///
    Key
    	possibleCancelations
	(possibleCancelations,HashTable)
    Headline
    	returns the list of all possible abstract Betti tables, as HashTables, arrising from 
	a particular table via cancelations
    Usage
    	L = possibleCancelations(H)
    Inputs
    	H:HashTable
	    representing a Betti table
    Outputs
    	L:List
	    containing the possible abstract Betti tables arrising via cancelations
    Description
    	Text
	    Given a HashTable representing an (abstract) Betti table this returns the 
	    list of all possible abstract Betti tables arrising via cancelations.

	Example
	    H = new HashTable from {(0,0) => 1, (0,1) => 0, (1,0) => 0, (2,0) => 0, (0,2) => 0, (1,1) => 6, (3,0) => 0, (2,1) => 8, (1,2) => 0, (3,1) => 3, (2,2) => 0, (3,2) => 0};
	    makeBettiFromHash(H) 	
///

doc ///
    Key
    	possibleBettiTables
	(possibleBettiTables,HashTable)
    Headline
    	returns the list of all possible abstract Betti tables, as HashTables, arrising from 
	a particular table via cancelations
    Usage
    	L = possibleBettiTables(H)
    Inputs
    	H:HashTable
	    representing a Betti table
    Outputs
    	L:List
	    containing the possible abstract Betti tables arrising via cancelations
    Description
    	Text
	    Given a HashTable representing an (abstract) Betti table this returns the 
	    list of all possible abstract Betti tables arrising via cancelations.

	Example
	    H = new HashTable from {(0,0) => 1, (0,1) => 0, (1,0) => 0, (2,0) => 0, (0,2) => 0, (1,1) => 6, (3,0) => 0, (2,1) => 8, (1,2) => 0, (3,1) => 3, (2,2) => 0, (3,2) => 0};
	    makeBettiFromHash(H) 	
///

TEST ///
    R = QQ[x_{0},x_{1},x_{2},x_{3}]
    I = ideal(x_{1}*x_{2}-x_{0}*x_{3}
    assert ( sub(segreIdeal({1,1}),R) == I)
///
end


searchCone(H)


tb40 = new HashTable from {(5,2) => 0, (6,1) => 7920, (7,0) => 0, (8,0) => 0, (6,2) => 0, (7,1) => 6237, (9,0) => 0, (8,1) => 3344, (7,2) => 0, (10,0) => 0, (9,1) => 1089, (8,2) => 0, (11,0) => 0, (10,1) => 120, (9,2) => 0, (12,0) => 0, (11,1) => 0, (10,2) => 55, (12,1) => 0, (11,2) => 24, (12,2) => 3, (0,0) => 1, (0,1) => 0, (1,0) => 0, (2,0) => 0, (0,2) => 0, (1,1) => 75, (3,0) => 0, (2,1) => 536, (1,2) => 0, (3,1) => 1947, (2,2) => 0, (4,0) => 0, (3,2) => 0, (4,1) => 4488, (5,0) => 0, (4,2) => 0, (5,1) => 7095, (6,0) => 0};
H = new HashTable from {{(0,0),1},{(1,0),0},{(2,0),0},{(3,0),0},{(0,1),0}, {(1,1),3}, {(2,1),8}, {(3,1),3}, {(0,2),0},{(1,2),9}, {(2,2),9}, {(3,2),3}}
