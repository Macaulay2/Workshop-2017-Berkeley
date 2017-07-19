
newPackage(
  "MultiHilbertPolynomial",
  AuxiliaryFiles => false,
  Version => "0.1",
  Date => "19 July 2017",
  Authors => {{
      Name => "Chris Eur", 
      Email => "chrisweur@gmail.com", 
      HomePage => "https://math.berkeley.edu/~ceur"}},
  Headline => "computes multigraded Hilbert polynomial",
  PackageExports => {},
  PackageImports => {},
  DebuggingMode => true,
  Reload => true
)

export {
    "multigradedHilbertPolynomial"       
}


multigradedHilbertPolynomial = method()
multigradedHilbertPolynomial (Ideal) := RingElement => I -> (
    hilbertPolynomial(I, Projective => false)
)



end


load "MultiHilbertPolynomial.m2"
R = QQ[x,y,z];
I = ideal"x2,y3";
multigradedHilbertPolynomial(I)

