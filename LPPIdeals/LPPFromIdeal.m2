loadPackage "LexIdeals"
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





LPPNonFullPowers = method(TypicalValue=>Ideal)
LPPNonFullPowers(PolynomialRing,List,List) := (R,hilb,powers) -> (
     numvars:=dim R;
     m:=ideal vars R;
     if #powers != numvars then return null;
     if not isNonDec(powers) then return null;
     if not isHF(hilb) then return null;
     gen:=toList apply(0..(#powers-1),i->(R_i)^(powers#i));
     lppIdeal:=ideal gen;
     hilbGens:=hilbertFunct lppIdeal;
     hilbSameLength:=makeSameLength(hilbGens,hilb);
     toAdd:=hilbSameLength#0-hilbSameLength#1; --number of mons we need to add
     deg:=1;                                   --in each degree
     --continue in while loop while the toList is not all 0's and has all
     --nonnegative entries
     while toAdd != toList (#toAdd:0) and toAdd >= toList (#toAdd:0) do (
	  if toAdd#deg == 0 then deg=deg+1 else (
	       mons:=flatten entries basis(deg,coker gens lppIdeal);
	       --select the monomials not already in lppIdeal
	       addMons:=take(mons,toAdd#deg);
	       if not all(addMons,i->(not isPurePower i)) then return null;
	       if #addMons != toAdd#deg then return null;
	       gen=join(gen,addMons);
	       lppIdeal=ideal gen;
	       hilbGens=hilbertFunct(ideal gen);
     	       hilbSameLength=makeSameLength(hilbGens,hilb);
     	       toAdd=hilbSameLength#0-hilbSameLength#1;
	       );
     );
     if (toAdd != toList (#toAdd:0)) then return null
     else lppIdeal
)

LPPNonFullPowers(Ideal) := (I) -> (
  powers := minregdeg(I);
  R:=ring I;
  if I == ideal(0_R) then return I;
  if dim I == 0 then return lexIdeal(R,hilbertFunct I) else (
       highGen:=max flatten degrees module ideal leadTerm I;
       deg:=highGen;
       done:=false;
       while done == false do (
          hilb:=hilbertFunct(I,MaxDegree=>deg+2);
          artinian:=LPPNonFullPowers(R,drop(hilb,{deg+2,deg+2}),powers);
    if not isIdeal artinian then return null;
          hfArtinian:=hilbertFunct(artinian,MaxDegree=>deg+1);
          lex:=ideal select(flatten entries gens artinian,i->first degree i <= deg);
          if (hilbertFunct(lex,MaxDegree=>deg+1))#(deg+1) == hfArtinian#(deg+1) then done=true;
          deg=deg+10;
          );
       return lex;
       );
  )
