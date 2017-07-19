-- -*- coding: utf-8-unix -*-
-- Code for Simplicial Complexes

--------------------------------------------------------------------------------
-- Copyright 2006, 2010  Sorin Popescu, Gregory G. Smith, and Mike Stillman
-- 
-- You may redistribute this program under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2 of the
-- License, or any later version.
--------------------------------------------------------------------------------

-- Janko added class Face to be used in other packages
-- should not affect the functionality present previously

newPackage(
	"SimplicialComplexesTemp",
    	Version => "1.0", 
    	Date => "July 19, 2017",
    	Authors => {
	     {Name => "Jason McCullough", Email => "jmccullo@iastate.edu"}
	     },
    	Headline => "simplicial complexes add ones (temporary file)",
    	DebuggingMode => false
    	)

needsPackage "SimplicialComplexes"

