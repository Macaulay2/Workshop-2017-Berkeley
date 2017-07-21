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
orientedMatroid = method(Options => {})

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
orientedMatroid (List,List) := Matroid => opts -> (E, B) -> (
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
	if opts.EntryMethod == "circuits" then (
		M.cache.circuits = B');  -- issue here chirotope is a hash table; circuits are vectors
	M
)


rankFromCircuits = method(Options => {symbol TargetRank => -1})
rankFromCircuits (List, ZZ) := (List, ZZ) => opts -> (C, n) -> (
	E := set(0..<n);
	t := if opts.TargetRank >= 0 then opts.TargetRank + 1 else max(C/(c -> #supp(c))); -- count nonzero entries of each circuit
        C'= unique(C/(c-> set supp(c)));
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
supp_pos = (circ) ->(  -- positive elements
    positions(circ, a -> a > 0)
    )
supp_neg = (circ) ->(  -- negative elements
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

-- input: B is a hash table whose keys are r-element subsets of {0,1,..,n}, whose values are +/-/0
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
    	if C_i =!= (-1)*(C_j) and  #((set supp_pos(C_i))*(set supp_neg(C_i)))>0	then	     	   scan((set supp_pos(C_i))*(set supp_neg(C_i)), e -> (
		found := false;
		scan(C, 
		    );
		)
	    );
		)
	    )
	);
    )

end
------------------------------------------
restart

loadPackage "OrientedMatroids"
A = matrix{{0,-1,1,1,2},{1,1,0,1,-1},{0,-1,0,-2,2},{1,0,0,-1,1}}
B = transpose gens kernel A
net matrix circuitsFromMatrix A
net matrix circuitsFromMatrix B

C = matrix{{0,0,0,0,1},{0,0,0,1,1},{1,2,3,4,5}}
matrix circuitsFromMatrix C
n = numColumns A; r = rank A;
H = chirotopeFromMatrix A
M =orientedMatroid(entries transpose A, H)
M.cache.chirotope

C = circuitsFromChirotope (H, n, r)
prod (C_0, C_1)
