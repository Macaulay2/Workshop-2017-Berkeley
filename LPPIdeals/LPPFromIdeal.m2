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
