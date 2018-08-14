TEST /// 
ZZ/5[x,y,z];
F = 2*x^7*y^3*z^8+2*x^4*z^9+2*x*y^7*z^4;
--
assert( nu(6,F) == 2968 ) 
assert( nu(6,F,ComputePreviousNus => false) == 2968 )
assert( nu(6,F,Search => BinaryRecursive) == 2968 )
assert( nu(6,F,Search => Linear) == 2968 )
assert( nu(6,F,UseColonIdeals=>true,ContainmentTest => StandardPower) == 2968 )
assert( nu(6,ideal F,UseColonIdeals=>true,ContainmentTest => StandardPower,Search => BinaryRecursive) == 2968 )
assert( nu(6,ideal F,UseColonIdeals=>true,ContainmentTest => StandardPower,Search => Linear) == 2968 )

assert( nuList(6,F) == {0, 0, 4, 23, 118, 593, 2968} ) 
assert( nuList(6,F,UseColonIdeals => true) == {0, 0, 4, 23, 118, 593, 2968} )  

 
ZZ/17[x,y,z,w];
F = -5*x*y^4*z^3-2*x^4*z^3*w+6*y*z^3*w^4+7*z*w^3-6*w^2;
--
assert( nu(2,F) == 220 ) 
assert( nu(2,F,ComputePreviousNus => false) == 220 )
assert( nu(2,F,Search => BinaryRecursive) == 220 )
assert( nu(2,F,Search => Linear) == 220 )
assert( nu(2,F,UseColonIdeals=>true,ContainmentTest => StandardPower) == 220 )
assert( nu(2,ideal F,UseColonIdeals=>true,ContainmentTest => StandardPower,Search => BinaryRecursive) == 220 )
assert( nu(2,ideal F,UseColonIdeals=>true,ContainmentTest => StandardPower,Search => Linear) == 220 )
assert( nu(3,F) == 3756 )  


ZZ/3[x,y,z];
I=ideal(x^2+y^3,y^2+z^3,z^2+x^3);
--
assert( nu(3,I) == 39 ) 
assert( nu(3,I,ComputePreviousNus => false) == 39 )
assert( nu(3,I,Search => BinaryRecursive) == 39 )
assert( nu(3,I,Search => Linear) == 39 )
assert( nu(3,I,UseColonIdeals => true,ContainmentTest => FrobeniusRoot) == 39 )

assert( nuList(3,I) == {0, 3, 12, 39} ) 
assert( nuList(3,I,UseColonIdeals => true) == {0, 3, 12, 39} ) 

assert( nu(5,I,ComputePreviousNus => false, ContainmentTest => FrobeniusPower) == 242 ) 
assert( nu(5,I,UseColonIdeals => true, ContainmentTest => FrobeniusPower) == 242 )

assert( nuList(5,I, ContainmentTest => FrobeniusPower) == {0, 2, 8, 26, 80, 242} ) 


ZZ/13[x,y,z];
I=ideal(x^3+y^4,y^6+z^3,z^5+x^7);
--
assert( nu(1,I) == 11 )
assert( nu(1,I,Search => Linear) == 11 )
assert( nu(1,I,ComputePreviousNus => false) == 11 ) 

time assert( nu(2,I, ContainmentTest => FrobeniusPower) == 154 ) 

ZZ/7[x,y,z];
I=ideal(x+y^2,y+z^2,z+x^2);
J=ideal(x^3,y^3,z^3);
time assert( nu(1,I,J) == 60 )
time assert( nu(1,I,J, ContainmentTest => FrobeniusPower) == 60) -- slow
time assert( newNu(1,I,J,ContainmentTest=>testRoot) == 60 ) -- better
time assert( newNu(1,I,J,ContainmentTest=>testRoot,Search=>Linear) == 60 ) 

time assert( nu(1,I,J, ContainmentTest => FrobeniusPower) == 48 ) -- old version
time assert( newNuHat(1,I,J,ComputePreviousNus=>false) == 48 )  
time assert( newNuHatList(1,I,J) == {6, 48} )  
time assert( newNuList(1,I,J,ContainmentTest=>testGenFrobeniusPower) == {6, 48} )  -- same as previous
///
