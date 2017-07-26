--multiplicativeOrder( ZZ, ZZ ) := ZZ => ( a, b ) ->
--(
--    if gcd( a, b ) != 1 then error "multiplicativeOrder: Expected numbers to be relatively prime.";
--    n := 1;
--    x := 1;
--    while (x = (x*a) % b) != 1 do n = n+1;
--    n	      
--)     



--*************************************************
--Partitions
--*************************************************

---------------------------------------------------------------------------------------
--- The following code was written in order to more quickly compute eth roots of (f^n*I)
--- It is used in fancyEthRoot
----------------------------------------------------------------------------------------
--- Find all ORDERED partitions of n with k parts

-- not used
allPartitions = ( n, k )->
(
	PP0:=matrix{ toList(1..k) };
	PP:=mutableMatrix PP0;
	allPartitionsInnards (n,k,PP,{})
)

allPartitionsInnards = ( n, k, PP, answer)->
(
	local i;
	if (k==1) then 
	(
		PP_(0,k-1)=n;
		answer=append(answer,first entries (PP));
	)
	else
	(
		for i from 1 to n-(k-1) do
		(
			PP_(0,k-1)=i;
			answer=allPartitionsInnards (n-i,k-1,PP,answer)	;	
		);
	);
	answer
)
