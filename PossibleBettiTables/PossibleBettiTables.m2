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
    "makeBetti",
    "isValidTable",
    "searchCone"
    "maxBetti",
    "maxBettiCyclic"
    }

maxBetti= method()
---the maximal betti table given a hilbert function and a ring
maxBetti(ZZ,List) := (n,h) -> (
       maxGradedBetti := (i,j)-> h_(j-i)*binomial(n,i);
       L := flatten apply(n+1,p->(apply(#h,q->{(p,q), maxGradedBetti(p,p+q)})));
       new HashTable from L
       )
     
maxBettiCyclic= method()
---the maximal betti table of a cyclic zero dimensional module with a given hilbert function
maxBettiCyclic(ZZ,List) := (n,h) -> (
    M := new MutableHashTable from maxBetti(n,h);
-- zeroing out first column under (0,0)
    for j from 1 to #h-1 do 
         (M#(1,j-1)= M#(1,j-1)-M#(0,j);
	  if M#(1,j-1) < 0 then (
	      error "Negative number in Betti Table \n
	      not valid Hilbert function");
	  M#(0,j)=0);
-- check for zeros
    for j from 0 to #h-1 do (
	for i from 1 to n do (
	    if M#(i-1,j) == 0 then (
		t = true;
		for k from 0 to j-1 do (
		    t = t and (M#(i-1,k) == 0);
		    );
		if t then (
		    for k from i to n do (
			if (j < #h-1) then (
			    M#(k-1,j+1) = M#(k-1,j+1)-M#(k,j);
			    if M#(k-1,j+1) < 0 then (
				error "Negative number in Betti Table
				\n not valid Hilbert function");
			    );
			M#(k,j) = 0
			);
		    );
		);
	    );
	);
	    
    new HashTable from M 
    )	

makeBetti = H ->(
    new BettiTally from apply(keys H, h-> (h_0,{h_0+h_1},h_0+h_1)=> H#h)
    )

isStrictlyIncreasing = L->(
     t:=true;
     for i from 0 to #L-2 do t=(t and (L_i<L_(i+1)));
     t)

isValidTable = method() 
isValidTable BettiTally := B -> (
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

searchCone = method()
searchCone (HashTable) := H ->(
    PD := (max(keys H))#0;
    U := apply(PD-1, i->H#(i+2,1));
    L := apply(PD-1, i->0);
    range := toList(L..U);
    delete(,apply(range, k->(
	M := new MutableHashTable from H;  
	apply(#k,i->(
		dif := M#(i+1,2)-M#(i+2,1);
	        M#(i+2,1)=(k#i);
		M#(i+1,2)=(k#i)+dif;
		));
	M = new HashTable from M;
	if isValidTable(makeBetti(M))==true then makeBetti M
    )))
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
    	maxBetti
    Headline
    	creates HashTable representing a Betti table of the maximum
	possible betti numbers
    Usage
    	H = maxBetti(n,lst)
    Inputs
    	n:ZZ
	    representing the dimension of a ring
	lst:List
	    representing the first nonzero values of the Hilbert
	    function
    Outputs
    	H:Hashtable
    Description
    	Text
	    Given an ZZ representing the dimension of a ring and
	    a list representing values of a Hilbert function this
	    returns a HastTable representing the maximum possible
	    betti numbers
	    
	Example
	    H = maxBetti(3,{1,3,3})	
///

///

doc ///
    Key
    	maxBettiCyclic
    Headline
    	creates HashTable representing a Betti table of the maximum
	possible betti numbers assuming the module is cyclic
    Usage
    	H = maxBettiCyclic(n,lst)
    Inputs
    	n:ZZ
	    representing the dimension of a ring
	lst:List
	    representing the first nonzero values of the Hilbert
	    function
    Outputs
    	H:Hashtable
    Description
    	Text
	    Given an ZZ representing the dimension of a ring and
	    a list representing values of a Hilbert function this
	    returns a HastTable representing the maximum possible
	    betti numbers assuming a cyclic module
	    
	Example
	    H = maxBettiCyclic(3,{1,3,3})	
///


doc ///
    Key
    	makeBetti
	(makeBetti,HashTable)
    Headline
    	turns the HashTable representing a Betti table into a BettiTally
    Usage
    	B = segreIdeal(H)
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
	    makeBetti(H) 	
///

doc ///
    Key
    	isValidTable
	(isValidTable,BettiTally)
    Headline
    	determines whether a given abstract Betti table is in the B-S cone
    Usage
    	t = isValidTable(B)
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
    	isValidTable
	(isValidTable,BettiTally)
    Headline
    	determines whether a given abstract Betti table is in the B-S cone
    Usage
    	t = isValidTable(B)
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


TEST ///
    R = QQ[x_{0},x_{1},x_{2},x_{3}]
    I = ideal(x_{1}*x_{2}-x_{0}*x_{3}
    assert ( sub(segreIdeal({1,1}),R) == I)

    H1 = new HashTable from {(0, 0) => 1, (0, 1) => 3, (0, 2) => 3,
	 (1, 0) => 3, (1, 1) => 9, (1, 2) => 9, (2, 0) => 3, (2, 1) => 9,
	 (2, 2) => 9, (3, 0) => 1, (3, 1) => 3, (3, 2) => 3}
    assert(sort(pairs(H1)) == sort(pairs(maxBetti(3,{1,3,3}))))
    
    H2 = new HashTable from {(0, 0) => 1, (0, 1) => 0,
	 (0, 2) => 0, (1, 0) => 0, (1, 1) => 3, (1, 2) => 9, (2, 0) => 0,
	 (2, 1) => 8, (2, 2) => 9, (3, 0) => 0, (3, 1) => 3, (3, 2) => 3}
    assert(sort(pairs(H2)) == sort(pairs(maxBettiCyclic(3,{1,3,3}))))
     
    H3 = new HashTable from {(0, 0) => 1, (0, 1) => 4,
	 (0, 2) => 10, (1, 0) => 4, (1, 1) => 16, (1, 2) => 40, 
	 (2, 0) => 6, (2, 1) => 24, (2, 2) => 60, (3, 0) => 4,
	 (3, 1) => 16, (3, 2) => 40, (4, 0) => 1, (4, 1) => 4,
	 (4, 2) => 10}
    assert(sort(pairs(H3)) == sort(pairs(maxBetti(4,{1,4,10}))))
    
    H4 = new HashTable from {(0, 0) => 1, (0, 1) => 0,
	 (0, 2) => 0, (1, 0) => 0, (1, 1) => 0, (1, 2) => 20, 
	 (2, 0) => 0, (2, 1) => 0, (2, 2) => 45, (3, 0) => 0,
	 (3, 1) => 0, (3, 2) => 36, (4, 0) => 0, (4, 1) => 0,
	 (4, 2) => 10}
    assert(sort(pairs(H4)) == sort(pairs(maxBettiCyclic(4,{1,4,10}))))
///
end

maxBetti(3,{1,3,3})
maxBettiCyclic(3,{1,3,3})
maxBetti(4,{1,4,10})

searchCone(H)


tb40 = new HashTable from {(5,2) => 0, (6,1) => 7920, (7,0) => 0, (8,0) => 0, (6,2) => 0, (7,1) => 6237, (9,0) => 0, (8,1) => 3344, (7,2) => 0, (10,0) => 0, (9,1) => 1089, (8,2) => 0, (11,0) => 0, (10,1) => 120, (9,2) => 0, (12,0) => 0, (11,1) => 0, (10,2) => 55, (12,1) => 0, (11,2) => 24, (12,2) => 3, (0,0) => 1, (0,1) => 0, (1,0) => 0, (2,0) => 0, (0,2) => 0, (1,1) => 75, (3,0) => 0, (2,1) => 536, (1,2) => 0, (3,1) => 1947, (2,2) => 0, (4,0) => 0, (3,2) => 0, (4,1) => 4488, (5,0) => 0, (4,2) => 0, (5,1) => 7095, (6,0) => 0};
H = new HashTable from {{(0,0),1},{(1,0),0},{(2,0),0},{(3,0),0},{(0,1),0}, {(1,1),3}, {(2,1),8}, {(3,1),3}, {(0,2),0},{(1,2),9}, {(2,2),9}, {(3,2),3}}
