newPackage( "Fsing",
Version => "0.1", 
Date => "May 30th, 2017", 
Authors => {
     {Name => "Erin Bela",
     Email=> "ebela@nd.edu"
     },
     {Name => "Alberto F. Boix",
     Email=> "alberto.fernandezb@upf.edu"
     },
     {Name => "David J. Bruce",
     Email => "djbruce@math.wisc.edu",
     HomePage => "http://www.math.wisc.edu/~djbruce/"
     },
     {Name => "Drew Ellingson",
     Email => "drewtell@umich.edu"
     },
     {Name => "Daniel Hernandez",
     Email => "dhernan@math.utah.edu",
     HomePage => "http://math.utah.edu/~dhernan/"
     },
     {Name => "Zhibek Kadyrsizova",
     Email => "zhikadyr@umich.edu"
     },
     {Name => "Mordechai Katzman",
     Email=> "m.katzman@sheffield.ac.uk",
     HomePage=> "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email=> "smalec@gsu.edu"
     },
     {Name => "Marcus Robinson",
     Email=> "robinson@math.utah.edu"
     },
     {Name => "Karl Schwede",
     Email => "schwede@math.psu.edu",
     HomePage => "http://math.utah.edu/~schwede/"
     },
     {Name => "Dan Smolkin",
     Email=> "smolkin@math.utah.edu"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
     },
     {Name=> "Emily Witt",
     Email=> "ewitt@umn.edu",
     HomePage => "http://math.umn.edu/~ewitt/"
     }
},
Headline => "A package for calculations of singularities in positive characteristic", 
DebuggingMode => true, 
Reload => true,
AuxiliaryFiles=>false
)

export{
    
--F-thresholds computations (FThresholds.m2)
    "BinaryFormCheck",
    "binarySearch1",
    "binarySearchRecursive",
    "BinomialCheck",
    "ComputePreviousNus",
    "DiagonalCheck", 
    "estFPT", --Karl (and others, Pedro?, maybe should just be called fpt?)
    "FinalCheck", 
    "fpt",   
    "fpt1",   
    "FPTApproxList",     
    "FTApproxList",
    "FTHatApproxList", 
    "guessFPT", --Karl (probably should be incorporated into estFPT
    "isFJumpingNumberPoly", --Karl (should be redone, so as not to assume a polynomial ring)
    "isFPTPoly", --Karl (should be redone, so as not to assume a polynomial ring)
    "linearSearch",
    "MultiThread",
    "newNu",
    "newNuHat", 
    "newNuHatList",
    "newNuList",   
    "nu",
    "nuAlt",
    "NuCheck",
    "nuHat",
    "nuHatList",
    "nuList",
    "nuListAlt",
    "nuListAlt1",
    "Origin",
    "OutputRange",
    "SearchFunction",
    "TestFunction",
    "testGenFrobeniusPower",
    "testPower",
    "testRoot",
    "UseColonIdeals",

--F-thresholds of special families of polynomials (SpecialFThresholds.m2)
    -- Eventually, only binomialFPT, diagonalFPT, and binaryFormFPT should  
    -- be exported from this section **PT
    "binaryFormFPT",     
    "binaryFormFPTInternal",
    "binomialFPT",
    "diagonalFPT",
    "factorList",    
    "findCPBelow",
    "isCP",
    "isInLowerRegion",
    "isInUpperRegion",
    "MaxExp",
    "Nontrivial",    
    "PrintCP",
    "setFTData",
    "splittingField",

 
-- Other
    "FFiniteSupport", ---MK
    "findAllCompatibleIdeals", ---MK	   
    "findGeneratingMorphisms", ---MK
    "FPureIdeals",
    "FullMap", ---Karl
    "generatingMorphism", ---MK
    "generatingRoot" ---MK
--    "paraTestModule", ---MK
--    "paraTestModuleAmbient" ---MK  
}

--*************************************************

load "./code/BasicFunctionsFPT.m2"

load "./code/FThresholds.m2"

load "./code/SpecialFThresholds.m2"

beginDocumentation()

load "./documentation/FThresholdsDoc.m2"

load "./documentation/SpecialFThresholdsDoc.m2"

-- TESTS

load "./tests/SpecialFThresholdsTest.m2"

