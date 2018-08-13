newPackage( "FThresholds",
Version => "0.1", 
Date => "May 30th, 2017", 
Authors => {
     {Name => "Erin Bela",
     Email => "ebela@nd.edu"
     },
     {Name => "Alberto F. Boix",
     Email => "alberto.fernandezb@upf.edu"
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
     Email => "m.katzman@sheffield.ac.uk",
     HomePage => "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email => "smalec@gsu.edu"
     },
     {Name => "Marcus Robinson",
     Email => "robinson@math.utah.edu"
     },
     {Name => "Karl Schwede",
     Email => "schwede@math.psu.edu",
     HomePage => "http://math.utah.edu/~schwede/"
     },
     {Name => "Dan Smolkin",
     Email => "smolkin@math.utah.edu"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
     },
     {Name => "Emily Witt",
     Email => "ewitt@umn.edu",
     HomePage => "http://math.umn.edu/~ewitt/"
     }
},
Headline => "A package for calculations of F-thresholds", 
DebuggingMode => true, 
Reload => true,
AuxiliaryFiles => true
)

needsPackage "TestIdeals"

export{
    
--F-thresholds computations (FThresholds.m2)
    "BinaryFormCheck",
    "BinaryRecursive",
    "BinomialCheck",
    "ComputePreviousNus",
    "criticalExponentApproximation",
    "DiagonalCheck", 
    "FinalCheck", 
    "fpt",   
    "FPTApproxList",
    "FrobeniusPower",
    "FrobeniusRoot",     
    "FTApproxList",
    "guessFPT", --Karl (probably should be incorporated into estFPT
    "HSL",	
    "isFJumpingNumber", --Karl (should be redone, so as not to assume a polynomial ring)
    "isFPT", --Karl (should be redone, so as not to assume a polynomial ring)
    "mu",
    "muList",
    "MultiThread",
    "nu",
    "NuCheck",
    "nuList",
    "Origin",
    "OutputRange",
    "Search",
    "StandardPower",
    "UseColonIdeals",

--F-thresholds of special families of polynomials (SpecialFThresholds.m2)
    -- Eventually, only binomialFPT, diagonalFPT, and binaryFormFPT should  
    -- be exported from this section **PT
    "binaryFormFPT",     
    "binaryFormFPTInternal",
    "binomialFPT",
    "diagonalFPT",
    "factorsAndMultiplicities",    
    "findCPBelow",
    "isCP",
    "isInLowerRegion",
    "isInUpperRegion",
    "MaxExp",
    "Nontrivial",    
    "PrintCP",
    "setFTData",
    "splittingField"
}

--*************************************************

load "./FThresholds/BasicFunctionsFPT.m2"

load "./FThresholds/FThresholds.m2"

load "./FThresholds/SpecialFThresholds.m2"

beginDocumentation()

load "./FThresholds/FThresholdsDoc.m2"

load "./FThresholds/SpecialFThresholdsDoc.m2"

-- TESTS

load "./FThresholds/SpecialFThresholdsTest.m2"

