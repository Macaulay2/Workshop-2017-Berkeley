newPackage(
    "randomIdeal",
    Version => "0.1",
    Date => "July 19, 2017",
    Authors => {{Name => "Lauren Cranton Heller",
	    Email => "lauren_heller@berkeley.edu"}},
    Headline => "my first Macaulay2 package",
    DebuggingMode => true
    )

needsPackage"SimpleDoc"

export {"randomCombo"}

randomCombo = method(TypicalValue=>Ideal)
randomCombo(Ideal,ZZ) := (I,n) -> (
    L=I_*;
    ideal apply(n,i->sum(L,j->random(ZZ)*j))
)
randomCombo(List,ZZ) := (M,n) -> (
    L=(ideal(M))_*;
    ideal apply(n,i->sum(L,j->random(ZZ)*j))
)

beginDocumentation()
doc ///
    Key
    	randomIdeal
    Headline
    	generates and intersects random ideals
    Description
    	Text
 ///

end

loadPackage(Reload=>true,"randomIdeal")
