doc ///
    Key
        HSLGModule
        (HSLGModule, Ring)
        (HSLGModule, Ring, Ideal)
        (HSLGModule, Ideal)
        (HSLGModule, ZZ, RingElement)
        (HSLGModule, QQ, RingElement)
        (HSLGModule, List, List)
        (HSLGModule, ZZ, List, List, Ideal)
    Headline
        computes the submodule of the canonical module stable under the image of the trace of Frobenius
    Usage
        HSLGModule(R)
        HSLGModule(R, canonicalIdeal)
        HSLGModule(canonicalIdeal)
        HSLGModule(t, f)
        HSLGModule(expList, eltList)
        HSLGModule(e, expList, eltList, canIdeal)
    Inputs 
        R:Ring
        canonicalIdeal:Ideal
        f:RingElement
        expList:List
        eltList:List
        e:ZZ
    Outputs
        :List
    Description
        Text
            Given a ring $R$ with canonical module $\omega$, this computes the image of $F^e_* \omega \to \omega$ for $e >> 0$.  This image is sometimes called the HSLG-module.  It roughly tells you where a ring is non-F-injective.
        Text
            Specifically, this function returns a list of the following entries.  {\tt HSLGmodule, canonicalModule, u, HSLCount} where {\tt canonicalModule} is the canonical module of the ring (expressed as an ideal), {\tt HSLGmodule} is a submodule of that canonical module, {\tt u} is an element of the ambient polynomial ring representing the trace of Frobenius on the canonical module and {\tt HSLCount} is how many times the trace of Frobenius was computed before the image stabilized.
        Example
            R = ZZ/7[x,y,z]/ideal(x^5+y^5+z^5);
            HSLList = HSLGModule(R);
            HSLList#1 --the ambient canonical module
            HSLList#0 --the HSLGsubmodule
            HSLList#2 --the element representing trace of Frobenius
            HSLList#3 --how many times it took until the image stabilized
        Text
            If you don't want the function to compute the canonicalModule, you can also pass it.  This can be useful if you pass it something other than the canonical module as well.
        Text
            Additionally, you can specify a pair $(R, f^t)$ as long as $t$ is a rational number without $p$ in its denominator.
        Example
            R = ZZ/7[x,y];
            HSLList = HSLGModule(5/6, y^2-x^3);
            HSLList#1 --the canonical module
            HSLList#0
            HSLList = HSLGModule(9/10, y^2-x^3);
            HSLList#0
///
