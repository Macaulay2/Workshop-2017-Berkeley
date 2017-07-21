restart
loadPackage"Visualize"
viewHelp"Visualize"

openPort "8080"

-- Graphs
G = graph({{0,1},{0,3},{0,4},{1,3},{2,3}},Singletons => {5})
visualize G
visualize( G, Verbose => true )
visualize(G, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)

cycleGraph 9
visualize oo

wheelGraph 8
visualize oo

generalizedPetersenGraph(3,3)
visualize oo

completeGraph(7)
visualize oo

cocktailParty(7)
visualize oo


-- Digraphs
G = digraph({ {1,{2,3}} , {2,{3}} , {3,{1}}})
visualize G

D1 = digraph ({{a,{b,c,d,e}}, {b,{d,e}}, {e,{a}}}, EntryMode => "neighbors")
visualize D1

D2 = digraph {{1,{2,3}}, {2,{4,5}}, {3,{5,6}}, {4,{7}}, {5,{7}},{6,{7}},{7,{}}}
visualize (D2, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)


-- Posets
P2 = poset {{1,2},{2,3},{3,4},{5,6},{6,7},{3,6}}
visualize( P2, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)
visualize(P2,FixExtremeElements => true)
visualize oo

-- Simplicial Complexes
R = ZZ[a..f]
D = simplicialComplex monomialIdeal(a*b*c,a*b*f,a*c*e,a*d*e,a*d*f,b*c*d,b*d*e,b*e*f,c*d*f,c*e*f)
visualize D

R = ZZ[a..g]
D2 = simplicialComplex {a*b*c,a*b*d,a*e*f,a*g}
visualize( D2, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)

R = ZZ[a..f]
L =simplicialComplex {d*e*f, b*e*f, c*d*f, b*c*f, a*d*e, a*b*e, a*c*d, a*b*c}
visualize L

-- Not Working (Bummer)
-- Ideals
S = QQ[x,y]
I = ideal"x4,xy3,y5"
visualize I
visualize( I, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)

R = QQ[x,y,z]
J = ideal"x4,xyz3,yz2,xz3,z6,y5"
visualize( J, VisPath => "/Users/bstone/Desktop/Test/", Warning => false)

closePort()
