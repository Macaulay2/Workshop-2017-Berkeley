newPackage( "TestIdeals",
Version => "0.1", 
Date => "May 30th, 2017", 
Authors => {
     {Name => "Erin Bela",
     Email => "ebela@nd.edu"
     },
     {Name => "Alberto F. Boix",
     Email => "alberto.fernandezb@upf.edu"
     },
     {Name => "Juliette Bruce",
     Email => "juliette.bruce@math.wisc.edu",
     HomePage => "https://juliettebruce.github.io/"
     },
     {Name => "Drew Ellingson",
     Email => "drewtell@umich.edu"
     },
     {Name => "Daniel Hernandez",
     Email => "hernandez@ku.edu",
     HomePage => "https://hernandez.faculty.ku.edu"
     },
     {Name => "Zhibek Kadyrsizova",
     Email => "zhikadyr@umich.edu"
     },
     {Name => "Mordechai Katzman",
     Email => "m.katzman@sheffield.ac.uk",
     HomePage => "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email => "malec@hood.edu"
     },
     {Name => "Matthew Mastroeni",
     Email => "mastroe2@illinois.edu"
     },
     {Name => "Maral Mostafazadehfard",
     Email => "maralmostafazadehfard@gmail.com"
     },
     {Name => "Marcus Robinson",
     Email => "robinson@math.utah.edu"
     },
     {Name => "Karl Schwede",
     Email => "schwede@math.utah.edu",
     HomePage => "http://math.utah.edu/~schwede/"
     },
     {Name => "Dan Smolkin",
     Email => "smolkin@math.utah.edu"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
     },
     {Name=> "Emily Witt",
     Email => "witt@ku.edu",
     HomePage => "https://witt.faculty.ku.edu"
     }
},
Headline => "A package for calculations of singularities in positive characteristic", 
DebuggingMode => true, 
Reload => true,
AuxiliaryFiles=>false
)

export{
--BasicFunctions (BasicFunctions.m2) 
    "adicExpansion",    
    "adicDigit", 	   
    "adicTruncation",
    "decomposeFraction",
    "floorLog",
    "multiplicativeOrder",
    "NoZeroC", --option to force certain behavior from a function
        
--ethRootFunctions (EthRoots.m2)
    "ascendIdeal", --Karl (still needs more tests / documentation)
    "AscentCount",
    --"boundLargestCompatible", ---MK (now in Fpure)
    "FrobeniusRootStrategy",  
    "frobeniusRoot",  
    "MonomialBasis",	
    "Substitution",
    
--Frobenius Powers (frobeniusPowers.m2)
    "fastExponentiation",
    "frobenius",
    "frobeniusPower",
    "FrobeniusPowerStrategy",
    "Naive", 
    "Safe", 
    
-- parameterTestIdeal.m2
    "AssumeCM", --an option for function, if true, then the function will do less work.
    "AssumeReduced", --an option telling functions to assume a ring is reduced.
    "AssumeNormal", --an option telling functions to assume a ring is normal.
    "AssumeDomain", --an option telling functions to assume a ring is a domain.
    "canonicalIdeal", --Karl (still needs more tests / documentation), this is based on Moty's old code.
    "findSplittingsOfIdeal", --Karl (this is Moty's find u function, but it returns a list if Macaulay2 doesn't identify 1 element).
    "isCohenMacaulay", --Karl (added recently, if anyone has ideas to improve this...)
    "isFrational", --Karl (added recently).
    "IsLocal", --an option for isCohenMacaulay, isFrational, etc.
--    "randomSubset", probably should not be exported
    "testModule", --Karl (this subsumes a bunch of older functions)
    "MTries",
    "parameterTestIdeal",
    
-- Finjective.m2
    "HSLGModule", --produces the non-F-injective module, ie the submodule of the canonical module
    "isFinjective",
    "CanonicalStrategy", --how to check F-injectivity on the canonical module (Ext or Katzman)
    "Katzman", --an option for CanonicalStrategy

-- testIdeals.m2
    "findQGorGen", --Karl (this finds y such that I^{[p^e]} : I = (y) + I^{[p^e]}, if it exists) **Documented**
    "testElement", --Karl (my students Marcus and Dan did some improvements on this recently, it doesn't compute the whole Jacobian, it just looks at random minors until it finds a good one, it can be much much faster) **Documented**
    "MaxCartierIndex", --the cartier index limfindAllCompatibleIdealsit in the test ideal method
    "testIdeal", --Karl (the new version)
    "QGorensteinIndex", --if you already know the Q-Gorenstein index, you can pass it
    "isFregular",
    "isFpure",

-- Other.m2
--    "HSL", 
--    "imageOfRelativeCanonical",
--    "imageOfTrace", --doesn't work! 
--    "isFPure",  
--    "isFRegularPoly",  --Karl : this should be removed / replaced with isFRegular
--    "isFRegularQGor",  --Karl : this should be removed / replaced with isFRegular
--    "isMapSplit",
--    "isSharplyFPurePoly", --Karl needs to be redone
--    "sigmaAOverPEMinus1Poly",  --Karl needs to be redone
--    "sigmaAOverPEMinus1QGor",  --Karl needs to be redone 
--    "sigmaQGorAmb", --Karl needs to be redone

--REMOVE LATER (DivisorPatch.m2)
--MTries = MTries;
--NoStrategy = "NoStrategy";
--ReturnMap = "ReturnMap";
--IdealStrategy = "IdealStrategy";
--Section = "Section";
--KnownDomain = "KnownDomain";
--IsGraded = "IsGraded"; 
--ModuleStrategy = "ModuleStrategy";

 
-- Other
    "FFiniteSupport", ---MK
    "findAllCompatibleIdeals", ---MK	   
    "findGeneratingMorphisms", ---MK
--    "FPureIdeals",
    "generatingMorphism", ---MK
    "generatingRoot" ---MK
--    "paraTestModule", ---MK
--    "paraTestModuleAmbient" ---MK  

}

--*************************************************
--*************************************************
--This is the revised (and cleaned up) version
--of the PosChar package, which has been under 
--continuous development since the Wake Forest 
--Macaulay2 workshop of August 2012.
--Only well documented and working functions are 
--migrated to this package.
--*************************************************
--*************************************************

load "./code/BasicFunctions.m2"

load "./code/EthRoots.m2"

load "./code/generatingMorphism.m2"

load "./code/frobeniusPowers.m2"

load "./code/compatiblySplit.m2"

--load "./code/FPure.m2"

load "./code/FFiniteSupport.m2"

load "./code/parameterTestIdeal.m2"

load "./code/Finjective.m2"

load "./code/testIdeals.m2"

load "./code/DivisorPatch.m2"

beginDocumentation()

load "./documentation/BasicFunctionsDoc.m2"

load "./documentation/frobeniusPowersDoc.m2"

load "./documentation/FsingDoc.m2"

load "./documentation/EthRootsDoc.m2"

load "./documentation/compatiblySplitDoc.m2"

load "./documentation/FFiniteSupportDoc.m2"

load "./documentation/generatingMorphismDoc.m2"

load "./documentation/testIdealsDoc.m2"

load "./documentation/parameterTestIdealDoc.m2"

load "./documentation/FinjectiveDoc.m2"

--load "./documentation/FPureDoc.m2"

-- TESTS

load "./tests/BasicFunctionsTest.m2"

load "./tests/EthRootsTest.m2"

load "./tests/frobeniusPowersTest.m2"

load "./tests/ParameterTestIdealTest.m2"

load "./tests/CompatiblySplitTest.m2"

end
