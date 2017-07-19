doc ///
    Key
        findQGorGen
        (findQGorGen, ZZ, Ring)
        (findQGorGen, Ring)
    Headline
        finds an element representing the Frobenius trace map of a Q-Gorenstein ring
    Usage
        findQGorGen(e, R)
        findQGorGen(R)
    Inputs
        e: ZZ
        R: Ring
    Outputs
        :RingElement
    Description
        Text
            Suppose that $R$ is a ring such that $(p^e-1)K_R$ is linearly equivalent to zero (for example, if $R$ is $Q$-Gorenstein with index not divisible by $p$).  Then if we write $R = S/I$ where $S$ is a polynomial ring, we have that $I^{[p^e]} : I = u S + I^{[p^e]}$ for some $u \in S$.  By Fedder's criterion, this element $u$ represents the generator of the $R^{1/p^e}$-module $Hom(R^{1/p^e}, R)$.  For example if $I = (f)$ is principal, then $u = f^{p^e-1}$ works.
        Text
            This function produces the element $f$ described above.  If do not specify an integer e, it assumes e = 1.
        Example
            S = ZZ/3[x,y,z];
            f = x^2*y - z^2;
            I = ideal(f);
            R = S/I;
            u = findQGorGen(1, R)
            u%I^3 == f^2%I^3
        Text
            If Macaulay2 does not recognize that $I^{[p^e]} : I / I^{[p^e]}$ is principal, an error is thrown.  Note in the nongraded case, Macaulay2 is not guaranteed to do this simplification.
///

doc ///
    Key
        testElement
        (testElement, Ring)
    Headline
        finds a test element of a ring
    Usage
        testElement(R)
    Inputs
        R: Ring
    Outputs
        :RingElement
    Description
        Text
            Given $R = S/I$ where $S$ is a polynomial ring, this finds an element of $S$ that restricts to a test element of $R$.  This does this by finding a minor of the Jacobian whose determinant is not in any minimal prime of the defining ideal of $R$.  It looks at random minors until one is found instead of computing all of them.
        Example
            R = ZZ/5[x,y,z]/(x^3+y^3+z^3);
            testElement(R)
            testElement(R)
            testElement(R)
///



doc ///
    Key
        testIdeal
        (testIdeal, Ring)
        (testIdeal, ZZ, RingElement)
        (testIdeal, QQ, RingElement)
        (testIdeal, ZZ, RingElement, Ring)
        (testIdeal, QQ, RingElement, Ring)
        (testIdeal, List, List)
        (testIdeal, List, List, Ring)
    Headline
        computes the test ideal of f^t in a Q-Gorenstein ring
    Usage
        testIdeal(t, f)
        testIdeal(t, f, R)
        testIdeal(Lexp, Lelts)
        testIdeal(Lexp, Lelts, R)        
    Inputs
        R: Ring
        t: QQ
        t: ZZ
        f: RingElement
        Lexp: List
        Lelts: List
    Outputs
        :Ideal
    Description
        Text
            Given a normal Q-Gorenstein ring $R$, passing the ring simply computes the test ideal $\tau(R)$.
        Example
            R = ZZ/5[x,y,z]/ideal(x^3+y^3+z^3);
            testIdeal(R)
        Example
            S = ZZ/5[x,y,z,w];
            T = ZZ/5[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            testIdeal(R)        
        Text
            Given a normal Q-Gorenstein ring $R$, a rational number $t \geq 0$ and a ring element $f \in R$, we can also compute the test ideal $\tau(R, f^t)$.
        Example
            R = ZZ/5[x,y,z];
            f = y^2 - x^3;
            testIdeal(1/2, f)
            testIdeal(5/6, f)
            testIdeal(4/5, f)
            testIdeal(1, f)
        Example
            R = ZZ/7[x,y,z];
            f = y^2 - x^3;
            testIdeal(1/2, f)
            testIdeal(5/6, f)
            testIdeal(4/5, f)
            testIdeal(1, f)
        Text
            It even works if the ambient ring is not a polynomial ring.
        Example
            R = ZZ/11[x,y,z]/ideal(x^2-y*z);
            f = y;
            testIdeal(1/2, f)
            testIdeal(1/3, f)
        Text
            Alternately, you can instead pass a list of rational numbers $\{t1, t2, ...\}$ and a list of ring elements $\{f1, f2, ...\}$.  In this case it will compute the test ideal $\tau(R, f1^{t1} f2^{t2} ...)$.
        Example
            R = ZZ/7[x,y];
            L = {x,y,(x+y)};
            f = x*y*(x+y);
            testIdeal({1/2,1/2,1/2}, L)
            testIdeal(1/2, f)
            testIdeal({2/3,2/3,2/3}, L)
            testIdeal(2/3, f)
            time testIdeal({3/4,2/3,3/5}, L)            
            time testIdeal(1/60, x^45*y^40*(x+y)^36)
        Text
            As above, frequently passing a list will be faster (as opposed to finding a common denominator and passing a single element) since the testIdeal can do things in a more intelligent way for such a list.
///

doc ///
    Key
        [testIdeal, FrobeniusRootStrategy]
    Headline
        controls the strategy for computing the Frobenius root of an ideal within the testIdeal call
    Usage
        testElement(..., FrobeniusRootStrategy=>S)
    Inputs
        S: Symbol
    Outputs
        :Ideal
    Description
        Text
            Valid options are Substitution and MonomialBasis.  These options will be passed in various other internal function calls.
///

doc ///
    Key
        [testIdeal, MaxCartierIndex]
    Headline
        sets the maximum Gorenstein index to search for when working with a Q-Gorenstein ambient ring
    Usage
        testElement(..., MaxCartierIndex=>N)
    Inputs
        N: ZZ
    Outputs
        :Ideal
    Description
        Text
            When working in a Q-Gorenstein ring, testIdeal must find an $N$ such that $N * K_R$ is Cartier.  This option controls the maximum value of $N$ to consider.  The default value is $100$.  If you pass it a ring such that the smallest such $N$ is less that MaxCartierIndex, then the function will throw an error.  This value is ignored if the user specifies the option QGorensteinIndex.
    SeeAlso
        [testIdeal, QGorensteinIndex]
///

doc ///
    Key
        [testIdeal, QGorensteinIndex]
    Headline
        specifies the Q-Gorenstein index of the ring
    Usage
        testElement(..., QGorenstein=>N)
    Inputs
        N: ZZ
    Outputs
        :Ideal
    Description
        Text
            When working in a Q-Gorenstein ring, testIdeal must find an $N$ such that $N * K_R$ is Cartier.  This option lets the user skip this search if this integer $N$ is already known.  Specifying a value $> 0$ will mean that MaxCartierIndex is ignored.
    SeeAlso
        [testIdeal, MaxCartierIndex]
///

doc ///
    Key
        QGorensteinIndex
    Headline
        an option used to specify the Q-Gorenstein index of the ring
    Description
        Text
            When working in a Q-Gorenstein ring frequently we must find an $N$ such that $N * K_R$ is Cartier.  This option lets the user skip this search if this integer $N$ is already known by setting QGorensteinIndex => N.
///

doc ///
    Key
        MaxCartierIndex
    Headline
        an option used to specify the maximum possible Cartier index of a divisor
    Description
        Text
            Some functions need to find the smallest value $N$ such that $N$ times a divisor is Cartier.  By specifying this value, the user controls what the maximal possible Cartier index to consider is.  
///
