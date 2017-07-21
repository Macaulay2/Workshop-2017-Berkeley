doc ///
     Key
     	 FPureIdeals
     Headline
         given a ring element $u$, finds all ideals $I$ such that $u I = I^{[p]}$
     Usage
     	 FPureIdeals(u)
     Inputs
	 u:RingElement
     Outputs
         :List
     Description
	 Text
	     Given a ring element $u$, find all ideals $I$ such that $u I = I^{[p]}$. 
             The ambient ring is assumed to be a polynomial ring over a prime field $F_p$. 
             This implements an algorithm described in Alberto F. Boix and 
             M. Katzman's "An algorithm for producing F-pure ideals" 
             Arch. Math. 103 (2014), 421-433.
///
