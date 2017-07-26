doc ///
     Key
     	generatingRoot
     Headline
        finds generating roots of F-Finite F-modules
     Usage
     	 generatingRoo(A,U)
     Inputs
	A:Matrix
	U:Matrix
     Outputs
         :Matrix
     Description
	Text
         Given a generating morphism $U:coker(A) \to F(coker A)$, compute a generating root $U:coker(L) \to F(coker L)$
///

doc ///
     Key
     	FFiniteSupport
     Headline
        finds supports of F-Finite F-modules
     Usage
     	 generatingRoot(A,U)
     Inputs
	A:Matrix
	U:Matrix
     Outputs
         :Matrix
     Description
	Text
         Finds the support of an F-finite F-module with generating morphism $U:coker(A) \to F(coker A)$, without computing a generating root. This implements the algorithm in M.Katzman and W. Zhang's "The support of local cohomology modules" (arXiv:1509.01519).
///

