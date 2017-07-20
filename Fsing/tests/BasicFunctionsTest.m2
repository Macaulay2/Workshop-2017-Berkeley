-- floorLog test#1 
TEST ///
time J = floorLog(2,3);
assert(J == 1)
///

-- multOrder test#1 
TEST ///
time J = multOrder(10, 7);
assert(J == 6)
///

-- divideFraction test#1 - (denominator a power of p)
TEST ///
time J = divideFraction(7, 19/49);
assert(J == {19, 2, 0} )
///

-- divideFraction test#2 - (denominator not power of p)
TEST ///
time J = divideFraction(2, 5/56);
assert(J == {5, 3, 3} )
///

-- divideFraction test#3 - (denominator not power of p)
TEST ///
time J = divideFraction(2, 5/24);
assert(J == {5, 3, 2} )
///

-- divideFraction test#4 - (negative)
TEST ///
time J = divideFraction(7, -19/49);
assert(J == { -19, 2, 0} )
///

-- adicDigit tests

TEST ///
time J = adicDigit(7, 2, 0);
assert(J == 0)
///

TEST ///
time J = adicDigit(13, 100, 1);
assert(J == 12)
///

TEST ///
time J = adicDigit(3, 2, 3/4);
assert(J == 0)
///

TEST ///
time J = adicDigit(3, 1, 3/4);
assert(J == 2)
///

TEST ///
time J = adicDigit(5, 3, 1/13);
assert(J == 4)
///

TEST ///
L = {3/4, 1/13};
time J = adicDigit(5, 3, L);
assert(J == {3,4})
///

-- adicExpansion tests 
TEST ///
time J = adicExpansion(2, 22);
assert(J == {0, 1, 1, 0, 1})
///

TEST ///
time J = adicExpansion(5, 399);
assert(J == {4, 4, 0, 3})
///

TEST ///
time J = adicExpansion(2, 4, 1/5);
assert(J == {0, 0, 1, 1})
///

TEST ///
time J = adicExpansion(7, 7, 1/19);
assert(J == {0, 2, 4, 0, 2, 4,0})
///

-- adicTruncation
TEST ///
time J = adicTruncation(7, 4, 1/19);
assert(J == 18/343)
///

TEST ///
time J = adicTruncation(7, 4, 1/29);
assert(J == 82/2401)
///

TEST ///
time J = adicTruncation(7, 4, {1/19, 1/29});
assert(J == {18/343, 82/2401)
///

-- carryTest - test#1
TEST ///
time J = carryTest(2, {1/4, 1/4});
assert(J == 3)
///


-- firstCarry test#1
TEST ///
time J = firstCarry(2, {1/4, 1/4});
assert(J == 3)
///

-- firstCarry test#2
TEST ///
time J = firstCarry(2, {1/2, 1/2});
assert(J == 2)
///

-- reciprocal test#1 - (integer)
TEST ///
V = {2, 3, 19};
time J = reciprocal(V);
assert(J == {1/2, 1/3, 1/19})
///

-- reciprocal test#2 - (rational)
TEST ///
V = {2, 1/3, 19};
time J = reciprocal(V);
assert(J == {1/2, 3, 1/19})
///

-- getCanVector test#1 - (list)
TEST ///
time J = getCanVector(3, 7);
assert(J == {0, 0, 0, 1, 0, 0, 0})
///

-- getNumAndDenom test#1
TEST ///
V = {2, -1/12, 1/5};
time J = getNumAndDenom(V);
assert(J == ({120, -5, 12}, 60))
///

-- taxicabNorm test#1 - (integer)
TEST ///
V = {2, -2, 3};
time J = taxicabNorm(V);
assert(J == 7)
///

-- taxicabNorm test#2 - (rational)
TEST ///
V = {1, 1/2, 3};
time J = taxicabNorm(V);
assert(J == 9/2)
///

-- xInt test#1 
TEST ///
time J = xInt(1, 1, -2, -2);
assert(J == 0)
///

-- allPartitions test#1
TEST ///
time J = allPartitions(3, 2);
assert(J == {{2, 1}, {1, 2}})
///

-- maxIdeal test#1
TEST ///
R = QQ[x, y, z]
time J = maxIdeal(R);
assert(J == monomialIdeal(x, y, z))
///
