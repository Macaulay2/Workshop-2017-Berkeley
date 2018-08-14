doc ///
     Key
          BinaryFormCheck
     Headline
          An option for the function fpt to check whether input is binary form. 
     Description
          Text
               If true, the input is a form in two variables (so that the function "binaryFormFPT" can then be used). 
	            Valid values are {\tt true} or {\tt false}.
     SeeAlso
          fpt
///

doc ///
     Key
          BinomialCheck
     Headline
          An option for the function fpt to check whether the input is a binomial polynomial. 
     Description
          Text
               Enables the user to check whether an input is a binomial in a polynomial ring.  Valid values are {\tt true} or {\tt false}.
     SeeAlso
          fpt
///

doc ///
     Key
          ComputePreviousNus
     Headline
          An option for nu and nuList
     Description
          Text
               Valid values are {\tt true} or {\tt false}
     SeeAlso
          nu
          nuList
///

doc ///
     Key
          ContainmentTest
     Headline
          An option for nu and nuList. 
     Description
          Text
               Specifies which test you use to check containment of powers of ideals. Valid values are {\tt FrobeniusPower, FrobeniusRoot}, and {\tt StandardPower}. 
///

doc ///
     Key
         criticalExponentApproximation
         (criticalExponentApproximation,ZZ,Ideal,Ideal)
         (criticalExponentApproximation,ZZ,RingElement,Ideal)
     Headline
        Gives a list of mu_I^J(p^d)/p^d for d=0,...,e.
     Usage
          criticalExponentApproximation(e,I,J)
          criticalExponentApproximation(e,f,J) 
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text 
             This returns a list of mu_I^J(p^d)/p^d for d = 0, ..., e.  The sequence {mu_I^J(p^d)/p^d} converges to the critical exponent of I or f with respect to J.       
///

doc ///
     Key
          DiagonalCheck
     Headline
          An option for the function fpt
     Description
          Text
               Enables the user to check whether the input is a diagonal polynomial, i.e., of the form x_1^(d_1) + ... + x_n^(d_n). 
	            Valid values are {\tt true} or {\tt false}
     SeeAlso
          fpt
///

doc ///
     Key
         fpt
     Headline
         Atempts to compute the F-pure threshold of a polynomial at the origin  
     Usage
          estFPT(f,e,FinalCheck=>V,Verbose=>W)
     Inputs
         f:RingElement
         e:ZZ
         V:Boolean
         W:Boolean
     Outputs
        L:List
        Q:QQ
     Description
          Text 
              This tries to find an exact value for the fpt.  If it can, it returns that value.  Otherwise it should return a range of possible values (eventually).  It first checks to see if the ring is binonmial or diagonal.  In either case it uses methods of D. Hernandez.  Next it tries to estimate the range of the FPT using nu's.  Finally, it tries to use this to deduce the actual FPT via taking advantage of convexity of the F-signature function and a secant line argument.  finalCheck is a Boolean with default value True that determines whether the last isFRegularPoly is run (it is possibly very slow).  If FinalCheck is false, then a last time consuming check won't be tried.  If it is true, it will be.  Verbose set to true displays verbose output.
///

doc ///
     Key
         fptApproximation
         (fptApproximation,ZZ,Ideal)
         (fptApproximation,ZZ,RingElement)
     Headline
         Gives a list of nu_I(p^d)/p^d for d=0,...,e.
     Usage
          fptApproximation(e,I)
          fptApproximation(e,f) 
     Inputs
         e:ZZ
         I:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text 
             This returns a list of nu_I(p^d)/p^d for d = 0, ..., e.  The sequence {nu_I(p^d)/p^d} converges to the F-pure threshold.        
///


doc ///
     Key
          FRegularityCheck
     Headline
          An option for the function fpt
     Description
          Text
               Enables the user to check whether the given pair is F-regular at the given maximal ideal 
	            (so that if not, the F-pure threshold can be determined from the F-signature function).
		    Valid values are {\tt true} or {\tt false}
     SeeAlso
          fpt
///


doc ///
     Key
         ftApproximation
         (ftApproximation,ZZ,Ideal,Ideal)
         (ftApproximation,ZZ,RingElement,Ideal)
     Headline
         Gives a list of nu_I^J(p^d)/p^d for d=0,...,e.
     Usage
         ftApproximation(e,I,J)
         ftApproximation(e,f,J) 
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text 
             This returns a list of nu_I^J(p^d)/p^d for d = 0, ..., e.  The sequence {nu_I^J(p^d)/p^d} converges to the F-threshold of I or f with respect to J.         
///

doc ///
     Key
        guessFPT 
     Headline
        Tries to guess the FPT in a really naive way (this should be improved).
     Usage
         guessFPT(f,e,d) 
     Inputs
         f:RingElement
         e:ZZ
         d:ZZ
     Outputs
        :List
     Description
        Text
             This tries to guess the FPT.  In particular, it computes the number nu such that nu/(p^e - 1) <= FPT < (nu+1)/p^e.  It then outputs a list of all rational numbers with denominators less than or equal to d, which lie in that range.  WARNING:  There are several improvements which should be made to this function to rule out many of the possibilies.
///

doc ///
     Key
        isFJumpingNumber 
        (isFJumpingNumber,QQ,RingElement)
     Headline
        Checks whether a given number is an F-jumping number
     Usage
         isFJumpingNumber(t,f,Verbose=>V)  
     Inputs
         t:QQ
         f:RingElement
         V:Boolean
     Outputs
        :Boolean
     Description
        Text
            Returns true if t is an F-jumping number, otherwise it returns false.
///
 
doc ///
     Key
        isFPT 
        (isFPT,QQ,RingElement)
     Headline
        Checks whether a given number is the FPT
     Usage
          isFPT(t,f,Verbose=>V,Origin=>W)  
     Inputs
        t:QQ
        f:RingElement
        V:Boolean
        W:Boolean
     Outputs
        :Boolean
     Description
        Text
             Returns true if t is the FPT, otherwise it returns false.  If Origin is true, it only checks it at the homogeneous maximal ideal.
///

 
doc ///
     Key
         nu
         (nu,ZZ,Ideal,Ideal)
         (nu,ZZ,Ideal)
         (nu,ZZ,RingElement,Ideal)
         (nu,ZZ,RingElement)
     Headline
        Gives $\nu_I^J(p^e)$ or $\nu_f^J(p^e)$
     Usage
          nu(e,I,J)
          nu(e,I)
          nu(e,f,J)
          nu(e,f) 
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :ZZ
     Description
        Text
            Given an ideal I in a polynomial ring k[x1, ..., xn], this function outputs the maximal integer nu such that I^nu is not in ideal J^[p^e].  If the input is (ZZ,Ideal) then the function computes the maximal integer nu such that I^nu in not in (x_1, ...,x_n)^[p^e]. If a RingElement is passed, it computes nu of the principal ideal generated by this element. This is used frequently to compute the F-pure threshold.
///

doc ///
     Key
          NuCheck
     Headline
          An option for the function fpt
     Description
          Text
               Valid values are {\tt true} or {\tt false}
     SeeAlso
          fpt
///

doc ///
     Key
         nuList
         (nuList,ZZ,Ideal,Ideal)
         (nuList,ZZ,Ideal)
         (nuList,ZZ,RingElement,Ideal)
         (nuList,ZZ,RingElement)
     Headline
        Lists nu_I^J(p^d)$ for d = 1,...,e
     Usage
          nuList(e,I,J)
          nuList(e,I)
          nuList(e,f,J)
          nuList(e,f) 
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :List
     Description
        Text
            Given an ideal I in a polynomial ring k[x1,...,xn], this function computes nu(d,I) for d = 0,...,e. If a RingElement is passed, it computes nu of the principal ideal generated by this element for d = 0,...,e.
///

doc ///
     Key
          OutputRange
     Headline
          An option for guessFPT
     Description
          Text
               Valid values are {\tt true} and {\tt false}
///

doc ///
     Key
          Search
     Headline
          An option for the functions nu and nuList
     Description
          Text
               Lets user specify the order in which ideal containment of powers are computed. Valid values are 
	            {\tt Binary, BinaryRecursive}, and {\tt Linear}. 
     SeeAlso
          nu
          nuList
///

doc ///
     Key
          UseColonIdeals
     Headline
          An option for nu and nuList
     Description
          Text
               Valid values are {\tt true} and {\tt false}. 
     SeeAlso
          nu
          nuList
///
