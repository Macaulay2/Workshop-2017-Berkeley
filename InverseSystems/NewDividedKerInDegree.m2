needsPackage "InverseSystems"

contractionImageInDegree = method()

contractionImageInDegree (ZZ, RingElement) := Ideal => (i,phi) -> (
    R := ring phi;
    ideal contract(symmetricPower(i,vars R),phi)
    )

contractionImageInDegree (ZZ, List) := Ideal => (i,L) -> (
    R := ring L#0;
    apply(L,phi -> ideal contract(symmetricPower(i,vars R),phi))
    )


contractionKernelInDegree = method()

contractionKernelInDegree (ZZ, RingElement) := Ideal => (i,phi) -> (
    I := inverseSystem(matrix{{phi}},DividedPowers=>true);
    super basis(i,I)
    )

contractionKernelInDegree (ZZ, List) := Ideal => (i,L) -> (
    if any(L, phi -> not isHomogeneous phi) then (error "Expected a list of homogeneous polynomials.");
    I := inverseSystem(matrix{L},DividedPowers=> true);
    super basis(i,I)
    )

doc ///
   Key
    contractionImageInDegree
    (contractionImageInDegree, ZZ, RingElement)
    (contractionImageInDegree, ZZ, List)
   Headline
    Computes the image of the action of homogeneous polynomials on elements of the divided powers algebra in a given degree
   Usage
    I = contractionImageInDegree(i, phi)
    I = contractionImageInDegree(i,L)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
   Outputs
    I: List
     a list of ideals
   Description
    Text
     Computes the image of the map from the ith symmetric power to divided powers 
     given by multiplication by the ring element or list of elements. 
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     psi = contractionImageInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3,y^3,z^3,x*y^2+y*z^2,z*x^2}
     psi = contractionImageInDegree(i,L)
     ///


doc ///
   Key
    contractionKernelInDegree
    (contractionKernelInDegree, ZZ, RingElement)
    (contractionKernelInDegree, ZZ, List)
   Headline
    Computes the kernel of the action of homogeneous polynomials on elements of the divided powers algebra in a given degree
   Usage
    I = contractionKernelInDegree(i, phi)
    I = contractionKernelInDegree(i,L)
   Inputs
    i: ZZ
     an integer
    phi: RingElement
     a homogeneous polynomial in a standard graded polynomial ring
    L: List
     a list of homogeneous elements of a standard graded polynomial ring
   Outputs
    I: Ideal
   Description
    Text
     Computes the degree i piece of the kernel of the map from symmetric powers to divided powers 
     given by multiplication by the ring element or list of elements. 
    Example
     S = ZZ/5[x,y,z]
     i = 2
     phi = x^3+y^3+z^3
     psi = contractionKernelInDegree(i,phi)
    Example
     S = ZZ/5[x,y,z]
     i = 2
     L = {x^3,y^3,z^3,x*y^2+y*z^2,z*x^2}
     psi = contractionKernelInDegree(i,L)
     ///
