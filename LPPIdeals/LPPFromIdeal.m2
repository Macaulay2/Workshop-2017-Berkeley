loadPackage("LexIdeals", Reload=>true)
minregdeg = method(TypicalValue=>List)
minregdeg(Ideal) := (I) ->
(
  Igens := sort flatten entries mingens I;
  Degrees := Igens / (g -> first degree g);
  accumulate := {};
  cumulativeIdeals := for gen in Igens list (accumulate = append(accumulate,gen); ideal(accumulate));
  heights := cumulativeIdeals / codim;
  lastheight := -1;
  numgens := #Igens;
  returner = {};
  for i from 0 to numgens - 1 do (
    if lastheight != heights_i then (
      returner = append(returner, Degrees_i);
    );
    lastheight = heights_i;
  );
  returner
)





LPPNew = method(TypicalValue=>Ideal)
LPPNew(PolynomialRing,List,List) := (R,hilb,powers) -> (
  numvars:=dim R;
  while (#powers < numvars) do (powers = append(powers, #hilb));
  LPP(R,hilb,powers)
)
LPPFromIdeal = method(TypicalValue=>Ideal)
LPPFromIdeal(Ideal) := (I) -> (
  powers := minregdeg(I);
  R:=ring I;
  if I == ideal(0_R) then return I;
  if dim I == 0 then return LPPNew(R,hilbertFunct I,powers) else (
       highGen:=max flatten degrees module ideal leadTerm I;
       deg:=highGen;
       done:=false;
       while done == false do (
          hilb:=hilbertFunct(I,MaxDegree=>deg+2);
          artinian:=LPPNew(R,drop(hilb,{deg+2,deg+2}),powers);
    if not isIdeal artinian then return null;
          hfArtinian:=hilbertFunct(artinian,MaxDegree=>deg+1);
          lex:=ideal select(flatten entries gens artinian,i->first degree i <= deg);
          if (hilbertFunct(lex,MaxDegree=>deg+1))#(deg+1) == hfArtinian#(deg+1) then done=true;
          deg=deg+10;
          );
       return lex;
       );
  )

  --local function for use in isLPP
--if mon is a pure power, returns {index of variable, exponent}
purePowerIndex = method(TypicalValue=>Boolean)
purePowerIndex(RingElement) := mon -> (
     expVector:=flatten exponents mon;
     if number(expVector,i->i!=0) > 1 then false else (
	  pos:=position(expVector,i->i!=0);
	  {position(expVector,i->i!=0),expVector#pos}
     )
)

--determine whether a list of numbers is nondecreasing
isNonDec = method(TypicalValue=>Boolean)
isNonDec(List) := (li) -> (
     len:=#li;
     pos:=0;
     result:=true;
     while result==true and pos < len-1 do (
  	  result=li#(pos+1)>=li#pos;
  	  pos=pos+1;
	  );
     result
)


  isLPPNonFull = method(TypicalValue=>Boolean)
  isLPPNonFull(Ideal) := (I) -> (
       ri:=ring I;
       numvars:=dim ri;
       m:=ideal vars ri;
       Igens:=first entries gens trim I;
       --check that the power sequence has right length and is nondecreasing
       powers:=select(Igens,i->isPurePower i);
       --if #powers != numvars then return false;
       expon:=apply(sort apply(powers,i->purePowerIndex i),i->i#1);
       if not (isNonDec expon) then return false;
       --nonPowers are not a power of a variable
       nonPowers:=select(Igens,i->not isPurePower i);
       if nonPowers=={} then return true; --if a CI with nondec. powers
       maxDeg:=first flatten max(apply(nonPowers,i->flatten degree i));
       deg:=1;
       while deg <= maxDeg do (
  	  --get the minimal generators in degree deg and find the smallest
  	  --in descending lex order that isn't a pure power
  	  nonPowersDeg:=select(nonPowers,i->(first flatten degree i)==deg);
  	  ringBasis:=flatten entries basis(deg,ri);
  	  lastPos:=position(reverse ringBasis,i->member(i,nonPowersDeg));
       	  if lastPos===null then deg=deg+1 else (
  	       normalPos:=binomial(numvars-1+deg,deg)-1-lastPos;
  	       lastGen:=ringBasis#normalPos;
  	       --check that all mons > than lastGen in desc. lex order
  	       --are in I
  	       if not all(0..normalPos,i->((ringBasis#i) % I)==0) then return false else deg=deg+1;
       	       );
  	  );
       true
  )
