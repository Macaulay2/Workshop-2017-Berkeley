needsPackage "Graphs"
needsPackage "Matroids"

newPackage("OrientedMatroids",
	Headline => "Oriented Matroids",
	Version => "0.1",
	Date => "July, 2017",
	Authors => {{Name => Sonja Mapes}, {Name => "Josephine Yu"}},
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
orientedMatroid = method(Options => {symbol EntryMethod => "bases", symbol TargetRank => -1})
orientedMatroid (List, List) := Matroid => opts -> (E, B) -> (
	if #B > 0 and not instance(B#0, Set) then B = B/(l -> set l)
	r := if opts.TargetRank >= 0 then opts.TargetRank else if #B > 0 then #(B#0) else -1 -- this seems wrong
	E' := set(0..<#E);
	N := {};
	B' := if opts.EntryMethod == "bases" then (
		if #B == 0 then error "There must be at least one basis element" else B
	) else if opts.EntryMethod == "circuits" then (
		if #B == 0 then {E'}
		else (
			(N, r) = nonbasesFromCircuits(B, #E, TargetRank => opts.TargetRank); -- have to fix this
			toList(set subsets(E', r) - N)
		)
	);
	M := new OrientedMatroid from {
		symbol ground => E',
		symbol groundSet => E,
		symbol rk => , -- how to put this in?
		cache => new CacheTable
	};
    	if opts.EntryMethod == "bases" then (
	    M.cache.bases = B);
	if opts.EntryMethod == "circuits" then (
		M.cache.circuits = B);
	M
)

-- needs to be adapted to our situation
nonbasesFromCircuits = method(Options => {symbol TargetRank => -1})
nonbasesFromCircuits (List, ZZ) := (List, ZZ) => opts -> (C, n) -> (
	E := set(0..<n);
	t := if opts.TargetRank >= 0 then opts.TargetRank + 1 else max(C/(c -> #c));
	N := toList set flatten((select(C, c -> #c < t))/(c -> subsets(E - c, t - 1 - #c)/(s -> c + s)));
	if opts.TargetRank >= 0 then return (N, opts.TargetRank);
	D := toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s)));
	Cmax := select(C, c -> #c == t);
	if #D + #Cmax == binomial(#E, t) then return (N, t-1) else N = join(D, Cmax);
	for i from t+1 to #E do (
		D = toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s)));
		if #D == binomial(#E, i) then return (N, i-1) else N = D;
	)
)

-- sign function
-- CAVEAT: may give random output if not in an ordered ring/field
sign = x ->
(   
    if x > 0 then 1 else if x < 0 then -1 else if x == 0 then 0
    )

------------------------------------------

-- input: 
basesFromMatrix = A -> (
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
circuitsFromBases = (H, n, r) -> (
    C = apply(subsets(n,r+1),  S -> 
	    apply(n, i -> (
		    pos = position(S, s -> s == i);
		    if pos =!= null then
		    	(-1)^pos * H#(drop(S,{pos,pos}))   
		    else 0 
		)
		)
	);
    sort unique(C | apply(C, c -> -1 * c))
    )


end
------------------------------------------
restart

A = matrix{{0,-1,1,1,2},{1,1,0,1,-1},{0,-1,0,-2,2},{1,0,0,-1,1}}
B = transpose gens kernel A
net matrix circuitsFromMatrix B
C = matrix{{0,0,0,0,1},{0,0,0,1,1},{1,2,3,4,5}}
matrix circuitsFromMatrix C
n = numColumns A; r = rank A;
H = basesFromMatrix A
circuitsFromBases (H, n, r)
