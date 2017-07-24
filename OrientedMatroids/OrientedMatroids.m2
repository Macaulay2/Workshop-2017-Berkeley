needsPackage "Graphs"
needsPackage "Matroids"

newPackage("OrientedMatroids",
	Headline => "Oriented Matroids",
	Version => "0.1",
	Date => "July, 2017",
	Authors => {{Name => "Sonja Mapes"}, {Name => "Josephine Yu"}},
	DebuggingMode => true
)
export {
    --Symbols--
    "rk",--(already exported in Matroids)
    "TargetRank",--(already exported in Matroids)
    "chirotope",
    "circuits",--(already exported in Matroids)
    "groundSet",--(already exported in Matroids)
    "ground",--(already exported in Matroids)
    "matroidMatrix",
    --Types--
    "Matroid",--(already exported in Matroids)
    "OrientedMatroid",
    --Functions--
    "orientedMatroid",
    "rankFromCircuits",
    "supp",
    "suppPos",
    "suppNeg",
    "sign",
    "chirotopeFromMatrix",
    "circuitsFromMatrix",
    "circuitsFromChirotope",
    "chirotopeFromCircuits",
    "matrixFromDigraph",
    "circuitsFromDigraph",
    "prod",
    "isCircuits"
    }
needsPackage "Graphs"

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

OrientedMatroid = new Type of HashTable

globalAssignment OrientedMatroid
net OrientedMatroid := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "OrientedMatroid"
)

-- TO DO
-- Define == 
-- get bases, (co)circuits, (co)vectors, etc from matrices, di-graphs, etc
-- check base/circuit/vector axioms
-----------------------------------


-- constructor


-- still need to finish adapting
orientedMatroid = method(Options => {symbol TargetRank => -1})
-- inputing chirotope
orientedMatroid (List, HashTable) := OrientedMatroid => opts -> (E, B) -> (
	--if #B > 0 and not instance(B#0, Set) then B = B/(l -> set l)
	--r := if opts.TargetRank >= 0 then opts.TargetRank else if #B > 0 then #(B#0) else -1 -- this seems wrong
	r := if opts.TargetRank >= 0 then opts.TargetRank else #((keys B)_0); 
	E' := set(0..<#E);
	M := new OrientedMatroid from {
		symbol ground => E',
		symbol groundSet => E,
		symbol rk => r , -- how to put this in?
		cache => new CacheTable
	};
    	M.cache.chirotope = B;
	M
)

-- 2nd list is circuits
orientedMatroid (List,List) := OrientedMatroid => opts -> (E, B) -> (
	--if #B > 0 and not instance(B#0, Set) then B = B/(l -> set l)
	--r := if opts.TargetRank >= 0 then opts.TargetRank else if #B > 0 then #(B#0) else -1 -- this seems wrong
	r := if opts.TargetRank >= 0 then opts.TargetRank else rankFromCircuits(B, #E); 
	E' := set(0..<#E);
	M := new OrientedMatroid from {
		symbol ground => E',
		symbol groundSet => E,
		symbol rk => r , -- how to put this in?
		cache => new CacheTable
	};
		M.cache.circuits = B;  -- issue here chirotope is a hash table; circuits are vectors
	M
)

-- from a matrix
orientedMatroid Matrix := Matroid => opts -> A -> (
	E := entries transpose A/(v -> transpose matrix{v});
	E' := set(0..<#E);
	r := rank A;
		M := new OrientedMatroid from {
		symbol ground => E',
		symbol groundSet => E,
		symbol rk => r , -- how to put this in?
		cache => new CacheTable
	};
		M.cache.matroidMatrix = A;  
	M
)



rankFromCircuits = method(Options => {symbol TargetRank => -1})
rankFromCircuits (List, ZZ) := (List, ZZ) => opts -> (C, n) -> (
	E := set(0..<n);
	t := if opts.TargetRank >= 0 then opts.TargetRank + 1 else max(C/(c -> #supp(c))); -- count nonzero entries of each circuit
        C':= unique(C/(c-> set supp(c)));
	N := toList set flatten((select(C', c -> #c < t))/(c -> subsets(E - c, t - 1 - #c)/(s -> c + s))); -- fills up small circuits to be of size t-1 which can't be bases
	if opts.TargetRank >= 0 then  return opts.TargetRank;
	D := toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s))); -- gives us things of size t that are not bases
	Cmax := select(C', c -> #c == t);
	if #D + #Cmax == binomial(#E, t) then return t-1 else N = join(D, Cmax);
	for i from t+1 to #E do (
		D = toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s)));
		if #D == binomial(#E, i) then return i-1 else N = D;
	)
)



-- support function returns nonzero spots in +/-/0 vector
supp = (circ) ->(
    positions(circ, a -> a != 0)
    )
suppPos = (circ) ->(  -- positive elements
    positions(circ, a -> a > 0)
    )
suppNeg = (circ) ->(  -- negative elements
    positions(circ, a -> a < 0)
    )



-- sign function
-- CAVEAT: may give random output if not in an ordered ring/field
sign = x ->
(   
    if x > 0 then 1 else if x < 0 then -1 else if x == 0 then 0
    )

------------------------------------------

-- input: 
chirotopeFromMatrix = A -> (
    	E := entries transpose A/(v -> transpose matrix{v});
        r := rank A;  -- maybe want to optimize this step more later
        cols := numColumns A;
        A1 := A;
        if(r < numRows A) then A1 = transpose gens gb transpose A;
	hashTable (apply(subsets(#E, r), s-> {s, sign det A1_(s) }))
	)
		
    
    
------------------------------------------
-- input: a matrix over QQ or RR
-- output: all sign circuits of the oriented matroid on the columns of the input matrix (possibly up to re-orientation)
-- CAVEAT: if the matrix does not have full row-rank, then the vectors may be reoriented
circuitsFromMatrix = A -> (
    r := rank A;
    cols := numColumns A;
    A1 := A;
    if(r < numRows A) then A1 = transpose gens gb transpose A; -- row echelon form; this may re-orient the vectors
    t := local t;
    R := (ring A)[t_0..t_(cols-1)];
    A2 := matrix{gens R} || A1;
    C := apply(select(flatten entries gens minors(r+1, A2), ff -> ff != 0), f -> apply(gens R, x -> sign coefficient(x,f)));
    sort unique(C | apply(C, c -> -1 * c))
    )

------------------------------------------

-- input: H is a hash table whose keys are r-element subsets of {0,1,..,n}, whose values are +/-/0
-- r = rank
-- n = size of ground set
circuitsFromChirotope = (H, n, r) -> (
    C := apply(subsets(n,r+1),  S -> 
	    apply(n, i -> (
		    pos := position(S, s -> s == i);
		    if pos =!= null then
		    	(-1)^pos * H#(drop(S,{pos,pos}))   
		    else 0 
		)
		)
	);
    sort unique(C | apply(C, c -> -1 * c))
    )

------------------------------------------
-- input: C = signed circuits of oriented matroid
-- r = rank
-- n = size of ground set
chirotopeFromCircuits = (C, n, r) -> (
    if #C==0 then return new HashTable from {toList(0..n-1)=>1};
    UC := unique apply(C,c->supp(c));--undirected circuits
    Sb := subsets(n,r);
    H := new MutableHashTable;--initialize hash table to store chirotope--
    Bases := {};
    ind := 0;
    --assign 0 to non-bases, collect bases
    while (ind<#Sb) do(
       current := Sb_ind;
       if any(UC,e->isSubset(e,set current)) then(
	   --assign 0 to current non-basis
	   H#current = 0;
	   ind = ind+1
	   )else(
	   Bases = append(Bases, current);
	   ind = ind+1
	   ));
   --initialize same and different sign graphs--
   sameSign := {};
   diffSign := {};
   E := toList(0..n-1);
   --get graphs of bases with same and different signs based on circuits--
   scan(UC, uc->(
	   circ := first select(1,C,c->(supp(c)==uc));
	   comp := E-set(uc);
	   scan(subsets(comp,r+1-(#uc)), T->(
		   R := sort join(uc,T);--circ is the unique circuit in R
		   --initialize positive and negative lists--
		   Pos := {};
		   Neg := {};
		   --separate relevant bases into negative and positive based on circ--
		   scan(uc,j->(
			   BN := R-set({j});
			   p := position(R,l->(l==j));
			   if (-1)^p*(circ_j)>0 then (Pos=append(Pos,BN)) else (Neg=append(Neg,BN));
			   ));
		   --put relevant bases into same sign and different sign graphs--
		   sameSign = join(sameSign,subsets(Pos,2),subsets(Neg,2));
		   diffSign = join(diffSign,flatten table(#Pos,#Neg,(i,j)->{Pos_i,Neg_j}));
		   ));
	   ));
   --Assign +1 to first basis
   H#(Bases_0) = 1;
   --Initialize list of bases already signed
   signed := {Bases_0};
   --initialize list of signed bases all of whose neighbors
   --have not yet been processed
   boundary := signed;
   notSigned := Bases-set(signed);
   while (#notSigned)>0 do(
       newBoundary := {};
       --flag to detect if boundary has no new neighbors
       qnb :=0;
       scan(boundary,B1->(
	       nbs := (unique flatten select(sameSign,e->isSubset({B1},e)))-set(signed);
	       nbd := (unique flatten select(diffSign,e->isSubset({B1},e)))-set(signed)-set(nbs);
	       newBoundary = unique join(newBoundary,nbs,nbd);
	       --increment flag if B1 has no unsigned neighbors
	       if (#(nbs)==0 and #(nbd)==0)then(
		   qnb =qnb+1;
		   )else(
		   --sign the unsigned neighbors of boundary basis B1
		   scan(nbs, B2->(
			   H#B2 = H#B1;
			   signed = append(signed,B2);
			   notSigned = notSigned-set({B2})
			   ));
		   scan(nbd, B2->(
			   H#B2=-(H#B1);
			   signed = append(signed,B2);
			   notSigned = notSigned-set({B2});
			   ));
		   )));
       --if newBoundary is empty and there are still unsigned bases then exchange condition
       --is violated
       if (qnb==length boundary) then (
	   error "Exchange condition on matroid bases is not satisfied"
	   )else(
	   boundary=newBoundary
	   )
       );
    --return the completed hashtable function
    new HashTable from H
    )

------------------------------------------

--Input: E, list of (oriented) edges of digraph
--Output: cellular differential from edges to vertices

matrixFromDigraph = E ->(
    V := unique flatten E;
    matrix table(V,E,(v,e)->(
	    if v==(first e) then (
		return -1
		)else(
		if v==(last e) then (
		    return 1
		    )else(
		    0
		    ))))
    )

------------------------------------------

--input: E, edges of digraph
--output: directed circuits of associated oriented matroid

circuitsFromDigraph = E->(
    M := matrixFromDigraph(E);
    circuitsFromMatrix(M)
    )



------------------------------------------

-- product of signed (co)vectors (non-commutative!)
prod = (v1, v2) -> (
    if #v1 =!= #v2 then error "The lists must have the same length"
    else apply(#v1, i -> if v1_i =!= 0 then v1_i else v2_i)
    )


-- check circuit axioms
-- C is a proposed list of signed circuits (a list of lists of 0/1/-1)
-- n is the size of the ground set
isCircuits = C -> (
    n := #(C_0); -- size of the ground set
    z := apply(n,i-> 0); -- zero vector
    posZero := position(C, c -> c == z);
    if(posZero =!= null) then (
	print "The zero vector is not a circuit.\n"; 
	return false;
	);
    minusC := apply(C, c-> -1 * c);
    if((set minusC) =!= (set C)) then (
	print "The negative of any circuit must also be a circuit.\n";
	return false;
	);
    scan(#C, i -> scan(i+1..#C-1, j -> (
	    if (isSubset(set supp(C_i), set supp(C_j)) or isSubset(set supp(C_j), set supp(C_i))) and C_i =!= (-1)*(C_j) then (
		print "Incomparability axiom fails with the following circuits\n";
	    	print (C_i, C_j);	
	    	return false;       		
		); 
	    )
	)
    );    
    scan(#C, i -> scan(i+1..#C-1, j -> (   
    	if C_i =!= (-1)*(C_j) and  #((set suppPos(C_i))*(set suppNeg(C_i)))>0	then	     	   
	scan((set suppPos(C_i))*(set suppNeg(C_i)), e -> (
		found := false;
		scan(C, Z -> (
		    if isSubset(set suppPos(Z), ((set suppPos(C_i))+(set suppPos(C_j))) - {e}) and isSubset(set suppNeg(Z), ((set suppNeg(C_i))+(set suppNeg(C_j))) - {e}) then (
			found = true;
			break;
			);	
			) 
		    );
		if not found then (
		    print "Weak elimination axiom fails with the following circuits:\n";
		    print (C_i, C_j);
		    return false;
		    );
		)
	    );
		)
	    )
	);
    return true;
    )

end
------------------------------------------
restart

loadPackage "OrientedMatroids"
A = matrix{{0,-1,1,1,2},{1,1,0,1,-1},{0,-1,0,-2,2},{1,0,0,-1,1}}
B = transpose gens kernel A
net matrix circuitsFromMatrix A
net matrix circuitsFromMatrix B

A = matrix{{0,0,0,0,1},{0,0,0,1,1},{1,2,3,4,5}}
matrix circuitsFromMatrix A
n = numColumns A; r = rank A;
H = chirotopeFromMatrix A
M =orientedMatroid(entries transpose A, H)
M.cache.chirotope

C = circuitsFromChirotope (H, n, r)
prod (C_0, C_1)

--check output from chirotopeFromCircuits function--
--random matrix
M=matrix {{-1, 2, 3, -1, 0}, {-1, 2, 0, 0, 1}};
--acyclic digraph on K4
E=sort subsets(4,2)
M=matrixFromDigraph(E)
--a simple digraph
E={{0,1},{0,2},{2,1},{2,3},{3,2}};
M=matrixFromDigraph E
--two disjoint three-cycles
E={{0,1},{1,2},{2,0},{3,4},{4,5},{5,3}};
M=matrixFromDigraph E

--checking chirotopeFromCircuits against chirotopeFromMatrix
r=rank M
n=numcols M
H1=chirotopeFromMatrix(M)
C = circuitsFromMatrix(M)
H2=chirotopeFromCircuits(C,n,r)
--may only be true up to sign...
H1===H2
