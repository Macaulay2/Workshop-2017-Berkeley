newPackage(
    "mikeloper",
    Version => "0.1",
    Date => "July 19, 2017",
    Authors => {{Name => "Mike Loper",
	    	Email => "loper012@umn.edu",
		HomePage => "http://www.math.umn.edu/~loper012"}},
    Headline => "an example Macaulay2 package",
    DebuggingMode => true
    )

needsPackage "SimpleDoc"
needsPackage "BoijSoederberg"

export {"firstFunction"}

firstFunction = method()
firstFunction List := List => lst -> pureBetti(lst)

beginDocumentation()
doc ///
    Key
    	mikeloper
    Headline
       	an example Macaulay2 package
    Description
    	Text
	    This package is my first try at creating a package
    Caveat
    	None
///

doc ///
    Key
    	firstFunction
	(firstFunction, List)
    Headline
    	a first trial function
    Usage
    	newlst = firstFunction lst
    Inputs
    	lst:List
    Outputs
    	newlst:List
	    a new list
    Description
    	Text
	    inputs a list describing a pure betti diagram
	    of a certain type and outputs a list of the
	    betti numbers of that type
	Example
	    firstFunction {0,2,3,4}
	    firstFunction {0,2,4,5}
///

TEST ///
    assert ( firstFunction {0,2,4,5} == {3, 10, 15, 8} )
///

end

More Documentation here!