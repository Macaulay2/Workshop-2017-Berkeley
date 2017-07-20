-- -*- coding: utf-8-unix -*-
-- Code for Simplicial Complexes Extras

--------------------------------------------------------------------------------
-- Copyright 2017  Jason McCullough
-- 
-- You may redistribute this program under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2 of the
-- License, or any later version.
--------------------------------------------------------------------------------

-- Janko added class Face to be used in other packages
-- should not affect the functionality present previously

newPackage(
	"SimplicialComplexesTemp",  -- MERGE ME number 2
    	Version => "1.0", 
    	Date => "July 19, 2017",
    	Authors => {
	     {Name => "Jason McCullough", Email => "jmccullo@iastate.edu"}, HomePage => "http://users.rider.edu/~jmccullough"
	     },
    	Headline => "simplicial complexes add-ons",
    	DebuggingMode => false,
	PackageExports=>{ "SimplicialComplexes"}
    	)



export {"poincareSphere"}

-- something stupid jason wrote

poincareSphere = method()
poincareSphere(Ring) := (F) -> (
    assert(isField F);
    X := symbol X;
    R := F[X_1..X_16];
    L := {{1,2,4,9},
	{1,2,4,15},
	{1,2,6,14},
	{1,2,6,15},
	{1,2,9,14},
	{1,3,4,12},
	{1,3,4,15},
	{1,3,7,10},
	{1,3,7,12},
	{1,3,10,15},
	{1,4,9,12},
	{1,5,6,13},
	{1,5,6,14},
	{1,5,8,11},
	{1,5,8,13},
	{1,5,11,14},
	{1,6,13,15},
	{1,7,8,10},
	{1,7,8,11},
	{1,7,11,12},
	{1,8,10,13},
	{1,9,11,12},
	{1,9,11,14},
	{1,10,13,15},
	{2,3,5,10},
	{2,3,5,11},
	{2,3,7,10},
	{2,3,7,13},
	{2,3,11,13},
	{2,4,9,13},
	{2,4,11,13},
	{2,4,11,15},
	{2,5,8,11},
	{2,5,8,12},
	{2,5,10,12},
	{2,6,10,12},
	{2,6,10,14},
	{2,6,12,15},
	{2,7,9,13},
	{2,7,9,14},
	{2,7,10,14},
	{2,8,11,15},
	{2,8,12,15},
	{3,4,5,14},
	{3,4,5,15},
	{3,4,12,14},
	{3,5,10,15},
	{3,5,11,14},
	{3,7,12,13},
	{3,11,13,14},
	{3,12,13,14},
	{4,5,6,7},
	{4,5,6,14},
	{4,5,7,15},
	{4,6,7,11},
	{4,6,10,11},
	{4,6,10,14},
	{4,7,11,15},
	{4,8,9,12},
	{4,8,9,13},
	{4,8,10,13},
	{4,8,10,14},
	{4,8,12,14},
	{4,10,11,13},
	{5,6,7,13},
	{5,7,9,13},
	{5,7,9,15},
	{5,8,9,12},
	{5,8,9,13},
	{5,9,10,12},
	{5,9,10,15},
	{6,7,11,12},
	{6,7,12,13},
	{6,10,11,12},
	{6,12,13,15},
	{7,8,10,14},
	{7,8,11,15},
	{7,8,14,15},
	{7,9,14,15},
	{8,12,14,15},
	{9,10,11,12},
	{9,10,11,16},
	{9,10,15,16},
	{9,11,14,16},
	{9,14,15,16},
	{10,11,13,16},
	{10,13,15,16},
	{11,13,14,16},
	{12,13,14,15},
	{13,14,15,16}};
    fac := apply(L,l->product apply(l,v->(X)_v));
    simplicialComplex fac)


