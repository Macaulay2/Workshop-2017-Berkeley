randomIdealElement = method()
randomIdealElement(ZZ, Ideal) := (d, I) -> (
  R := ambient ring I;
  Imingens := flatten entries mingens I;
  lowDegree := select(Imingens, g -> first degree g <= d);
  sum(lowDegree / (g -> g * random(d - first degree g, R)))
)

--heuristicCodim = method(TypicalValue=>ZZ)
heuristicCodim(Ideal) := I -> (
  myR:=ambient ring I;
  dimR:=dim myR;
  GLFs := for i from 1 to dimR list random(1,myR);
  Igens := sort flatten entries mingens I;
	GoodGens := {first Igens};
  DoneDegree := first degree first Igens - 1;
  for gen in drop(Igens, 1) do
  (
    CurrentDegree = first degree gen;
    if CurrentDegree > DoneDegree then (
      newgen = randomIdealElement(CurrentDegree, I);
      II = ideal(append(GoodGens, newgen) | take(GLFs, dimR - 1 - #GoodGens));
      if codim(II) < dimR then (
        DoneDegree = CurrentDegree
      )else (
        GoodGens = append(GoodGens, newgen)
      )
    )
  );
  #GoodGens
)
