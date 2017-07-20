restart
setRandomSeed 12345
-- First we construct an example
A = ZZ[x,y,u]
R = ZZ[y,x,z,MonomialOrder=>Lex]
phi = map(R,A,{x,y,1})
B = ZZ[y,x, MonomialOrder=>Lex]
C = ZZ[y]
deg = 4
zdeg = 3
use R
G1 = y^deg + sum for i from 0 to zdeg-1 list phi random(deg-1,A) * z^i
G2 = z^zdeg + sum for i from 0 to zdeg-1 list (random ZZ) * z^i
F = sub(resultant(G1,G2,z), B)
factor F

-- This example goes through the algorithm of Bertone-Cheze-Galligo for absolute factorization
-- First, one should check whether F is abs irred.  We worry about this later.
use B
pt = (1,2)
factor sub(F, {x=>pt_0, y=>pt_1})
p = 13
Bp = (ZZ/p) (monoid B)
Cp = (ZZ/p) (monoid C)
Fp = sub(F, Bp)
-- the polynomial Fp must factor with high probability.
--  if not: change the point pt, also use criteria for abs fac.
facs = factorize Fp
-- now, take a factor of minimal degree
  facs = facs/(f -> prepend(degree(y,f_1), f))//sort
  F1 = facs_0_2
  assert(degree(y,F) % degree(y,F1) == 0)
-- now specialize F1 to x=pt_0
  use ring F1
  g0 = sub(sub(F1, x => pt_0), Cp)
  Fp0 = sub(sub(Fp, x => pt_0), Cp)
  g1 = Fp0 // g0
  assert(Fp0 == g0 * g1)

  -- for the hensel lift we need the gcd of g0, g1
  (gcd1, u0, u1) = toSequence gcdCoefficients(g0,g1)
  if gcd1 != 1 then error "not random enough";
  u0 = sub(u0, C)
  u1 = sub(u1,C)
  g0 = sub(g0,C)
  g1 = sub(g1,C)
  use ring F
  F0 = sub(sub(F, x=>pt_0),C)
  assert(sub(F0, Cp) == Fp0)
  (F0 - g0*g1) % p == 0
  -- want to lift g0 * g1 == Fp0 to G0 * G1 == F0 mod p^N, some N.
  q = p

  for i from 1 to 7 do (
      GG = ((F0 - g0*g1)//q)%q;
      g0' = ((GG * u1)%g0)%q;
      g1' = ((GG * u0)%g1)%q;
      h0 = g0 + q * g0';
      h1 = g1 + q * g1'; 
      assert((F0 - h0*h1)%(q^2) == 0);
      BB = - ((h0 * u0 + h1 * u1 - 1)//q)%q;
      u0' = u0 + q * (((u0*BB)%h1)%q);
      u1' = u1 + q * (((u1*BB)%h0)%q);
      assert((h0*u0' + h1*u1')%(q^2) == 1);
      -- switch elements for the loop
      u0 = u0';
      u1 = u1';
      g0 = h0;
      g1 = h1;
      q = q*q;
      );

  assert((F0 - g0*g1) % q == 0)
  -- now get the constant term of F1
  use C
  N = 2^(2^10)
  a = sub(g0, y=>pt_1)

  M = matrix{append(for i from 0 to 3 list N*(a^i % p^(128)), N*p^(128))} || id_(ZZ^5)
  LLL M
  
  M = mutableIdentity(ZZ, 5)
  for i from 0 to 4 do M_(i,i) = 1
  for i from 0 to 3 do M_(i,i+1) = -a
  M_(4,4) = p^(2^5)
  M = transpose M
  LLL M

a = symbol a
kk = toField(QQ[a]/(a^2+a+1))  
R = kk[x]
factor(x^2+x+1)
