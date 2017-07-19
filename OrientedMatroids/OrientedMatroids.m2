needsPackage "Graphs"
needsPackage "Matroids"

newPackage("OrientedMatroids",
	Headline => "Oriented Matroids",
	Version => "0.1",
	Date => "July, 2017",
	Authors => {{Name => Sonja Mapes}, {Name => "Josephine Yu"}},
	DebuggingMode => true
)
export {

    }
needsPackage "Graphs"

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

OrientedMatroid = new Type of HashTable

globalAssignment OrientedMatroid
net OrientedMatroid := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "OrientedMatroid"
)

-- TO DO
-- Define == 
-----------------------------------

-- constructor
orientedMatroid = method(Options => {})




end
------------------------------------------
restart