doc ///
     Key
     	findAllCompatibleIdeals 
     Headline
        finds all compatibly Frobenius split ideals
     Usage
     	 findAllCompatibleIdeals(u)
     Inputs
	u:RingElement
            a polynomial with coefficients in a prime field {\tt ZZ/p}
     Outputs
         :List
     Description
	Text
	     Given an element $u$ of a polynomial ring $R$ {\bf over a prime field ZZ/p},
             this function returns a list of all prime ideals $P$ such that 
	     $u P \subseteq P^{[p]}$ and $u$ is not in $P^{[p]}$. The latter condition
             is equivalent to the non-vanishing of the corresponding Frobenius map on 
             annihilator of $P$ on the injective hull of the residue field of $R$. 
             This is an implementation of the algorithm described in Moty Katzman and 
             Karl Schwede's paper "An algorithm for computing compatibly Frobenius 
             split subvarieties", J. Symbolic Comput. 47 (2012), no. 8, 996-1008.
             The following is an example from that paper. 
     Description
	Example
	     R = ZZ/2[x_{21},x_{31},x_{32},x_{41},x_{42},x_{43}];
	     u = x_{41}*(x_{31}*x_{42}-x_{41}*x_{32})*(x_{41}-x_{21}*x_{42}-x_{31}*x_{43}+x_{21}*x_{32}*x_{43});
	     C = findAllCompatibleIdeals( u );
	     apply( C, print );

///


