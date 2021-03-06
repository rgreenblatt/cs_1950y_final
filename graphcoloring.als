//----------------------------------------------------------
//------------------------PREDICATES------------------------
//----------------------------------------------------------

sig Node {
    refs: set Node, -- undirected graph
    dists: set Node -> one Int, -- distances from node to all other nodes in orientation
    acOri: set Node -- acyclic orientation for the graph
}

sig Color {
    nodeColors: set Node -- defines the color of each node
}

-- graph is undirected and irreflexive
pred validSymmetric[graph : Node -> Node] {
    ~graph in graph
    no iden & graph
}

-- defines distance metric for each node
pred validDists[graph : Node->Node, graphDists : Node->Node->Int] {
    all u : Node | graphDists[u][u] = 0
    all disj u, v : Node | {
        v in u.(^graph) => graphDists[u][v] = add[max[u.graph.graphDists[v]], 1]
        v not in u.(^graph) => graphDists[u][v] = -1
    }
}

-- checks acOri is an acyclic orientation of the graph
pred validOrientation[graph : Node->Node, acOri : Node->Node] {
    acOri in graph
    all u: Node | {
        -- acyclic
        u->u not in ^acOri
         -- exactly one direction picked for each edge
        all v : u.graph | (u->v in acOri iff v->u not in acOri)
    }
}

-- ensures that no two adjacent nodes should have the same color
pred noAdjColors [graph : Node -> Node, coloring : Color -> Node]  {
    all n : Node | coloring.n not in coloring.(n.graph)
}

-- each node has exactly one color
pred oneColorPerNode[coloring : Color -> Node] {
    all n : Node | one n.(~coloring)
}

-- every node has a color and no adjacent nodes have the same color
pred validColoring [graph : Node -> Node, coloring : Color -> Node] {
    noAdjColors[graph, coloring]
    oneColorPerNode[coloring]
}

-- valid coloring and no more than k colors
pred validKColoring [graph : Node -> Node, coloring : Color -> Node, k : Int] {
    validColoring[graph, coloring]
    #(coloring.Node) <= k // number of "used" colors is k or lower
}

-- graph can be colored with k colors
pred kColorable [graph : Node -> Node, k : Int] {
    k >= 0
    some coloring : Color->Node | validKColoring[graph, coloring, k]
}

pred isChromaticNumber [graph : Node->Node, k : Int] {
    kColorable[graph, k]
    not kColorable[graph, minus[k, 1]]
}

fun longestPath[pathDists : Node->Node->one Int] : Int {
    max[Node.(Node.pathDists)]
}

pred minimalLongestLengthOrientation[graph : Node->Node, acOri : Node->Node,
    acDists : Node->Node->one Int] {
    validOrientation[graph, acOri]
    validDists[acOri, acDists]
    no otherAcOri : Node->Node when validOrientation[graph, otherAcOri] | {
        some otherAcDists : Node->Node->one Int when
            validDists[otherAcOri, otherAcDists] {
            longestPath[otherAcDists] < longestPath[acDists]
        }
    }
}

//----------------------------------------------------------
//------------------------TESTING---------------------------
//----------------------------------------------------------

pred empty {
    no Node
    no refs
    no dists
    no acOri
}

/* check {empty => validSymmetric[refs]} */

// Dirty hack to allow naming
sig Node0 extends Node {}
sig Node1 extends Node {}
sig Node2 extends Node {}
sig Node3 extends Node {}
sig Node4 extends Node {}
sig Node5 extends Node {}
sig Node6 extends Node {}
sig Node7 extends Node {}
sig Node8 extends Node {}
sig Node9 extends Node {}
sig Color0 extends Color {}
sig Color1 extends Color {}
sig Color2 extends Color {}
sig Color3 extends Color {}
sig Color4 extends Color {}
sig Color5 extends Color {}
sig Color6 extends Color {}
sig Color7 extends Color {}
sig Color8 extends Color {}
sig Color9 extends Color {}

pred oneOfEach {
    lone Node0
    lone Node1
    lone Node2
    lone Node3
    lone Node4
    lone Node5
    lone Node6
    lone Node7
    lone Node8
    lone Node9
    lone Color0
    lone Color1
    lone Color2
    lone Color3
    lone Color4
    lone Color5
    lone Color6
    lone Color7
    lone Color8
    lone Color9
}

pred single {
    oneOfEach
    Node = Node0
    #Node0 = 1
    no refs
    dists = Node0->Node0->0
    no acOri
    #Color0 = 1
    nodeColors = Color0->Node0
}

/* check {single => validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {single} */

pred twoSymmetric {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = Node0->Node1 + Node1->Node0
    dists = Node0->Node0->0 + Node1->Node1->0 + Node0->Node1->1 +
        Node1->Node0->1
    acOri = Node0->Node1
    #Color0 = 1
    #Color1 = 1
    nodeColors = Color0->Node0 + Color1->Node1
}

/* check {twoSymmetric => validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {twoSymmetric} */

pred twoDisconnected {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = none->none
    dists = Node0->Node0->0 + Node1->Node1->0 + Node0->Node1->-1 +
        Node1->Node0->-1
    acOri = none->none
    #Color0 = 1
    nodeColors = Color0->Node0 + Color0->Node1
}

/* check {twoDisconnected => validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {twoDisconnected} */

pred twoOneDirection {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = Node0->Node1
    dists = Node0->Node0->0 + Node1->Node1->0 + Node0->Node1->1 +
        Node1->Node0->-1
    no acOri
}

/* check {twoOneDirection => not validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {twoOneDirection} */

pred threeDistanceEdgeCase {
    oneOfEach
    Node = Node0 + Node1 + Node2
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    refs = Node0->Node1 + Node2->Node1
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node0->Node1->1 + Node0->Node2->-1 + Node1->Node0->-1 +
        Node1->Node2->-1 + Node2->Node0->-1 + Node2->Node1->1

    no acOri
}

/* check {threeDistanceEdgeCase => not validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {threeDistanceEdgeCase} */

pred mostlySymmetricMany {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->1 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->2 +
        Node1->Node3->2 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1
	no acOri
}

/* check {mostlySymmetricMany => not validSymmetric[refs]} */

// Verify some instance exists (some instance should exist)
/* run {mostlySymmetricMany} for 5 */

pred symmetricMany {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->-1 + Node0->Node2->3 + Node2->Node0->-1 +
        Node0->Node3->2 + Node3->Node0->-1 + Node0->Node4->-1 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->-1 +
        Node1->Node3->1 + Node3->Node1->-1 + Node2->Node3->-1 +
        Node3->Node2->1 + Node2->Node4->-1 + Node4->Node2->4 +
        Node3->Node4->-1 + Node4->Node3->3 + Node4->Node1->2 +
        Node1->Node4->-1

    acOri = Node0->Node1 +  Node0->Node2 + Node3->Node2 +  Node4->Node3 +
         Node4->Node0 +  Node1->Node3
    
    #Color0 = 1
    #Color1 = 1
    nodeColors = Color0->(Node0 + Node3) + Color1->(Node1 + Node2 + Node4)
}

// Verify some instance exists (some instance should exist)
//run {symmetricMany} for 5 Node, 5 Color

/* check {symmetricMany => validSymmetric[refs]} */

/* check {empty => validDists[refs, dists]} */
/* check {single => validDists[refs, dists]} */
/* check {twoDisconnected => validDists[refs, dists]} */
/* check {threeDistanceEdgeCase => validDists[refs, dists]} */
 // check {symmetricMany => validDists[acOri, dists]} 
pred mostlySymmetricManyWrongDist {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->1 +
        Node4->Node0->1 + Node1->Node2->3 + Node2->Node1->2 +
        Node1->Node3->2 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1
    no acOri
}

// Verify some instance exists (some instance should exist)
/* run {mostlySymmetricManyWrongDist} for 5 */

pred symmetricManyWrongDist {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->2 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->2 +
        Node1->Node3->1 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1
    no acOri
}

// Verify some instance exists (some instance should exist)
/* run {symmetricManyWrongDist} for 5 */

/* check {symmetricManyWrongDist => not validDists[refs, dists]} */

/* check {empty => validOrientation[refs, acOri]} */
/* check {single => validOrientation[refs, acOri]} */
/* check {twoSymmetric => validOrientation[refs, acOri]} */
/* check {twoDisconnected => validOrientation[refs, acOri]} */
/* check {symmetricMany => validOrientation[refs, acOri]} */

pred symmetricManyInvalidOrientationDup {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->1 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->2 +
        Node1->Node3->1 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1
    acOri = Node0->Node1 +  Node0->Node2 + Node3->Node2 +  Node4->Node3 +
         Node4->Node0 + Node1->Node3 + Node3->Node1
}

// Verify some instance exists (some instance should exist)
/* run {symmetricManyInvalidOrientationDup} for 5 */

/* check {symmetricManyInvalidOrientationDup => not validOrientation[refs, acOri]} for 5 */

pred symmetricManyInvalidOrientationMissing {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->1 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->2 +
        Node1->Node3->1 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1
    acOri = Node0->Node1 +  Node3->Node2 +  Node4->Node3 +
         Node4->Node0 + Node3->Node1
}

// Verify some instance exists (some instance should exist)
/* run {symmetricManyInvalidOrientationMissing} for 5 */

/* check {symmetricManyInvalidOrientationMissing => not validOrientation[refs, acOri]} for 5 */

/* check {empty => noAdjColors[refs, nodeColors]} */
/* check {single => noAdjColors[refs, nodeColors]} */
/* check {twoSymmetric => noAdjColors[refs, nodeColors]} */
/* check {twoDisconnected => noAdjColors[refs, nodeColors]} */
/* check {symmetricMany => noAdjColors[refs, nodeColors]} for 5 */

pred manyMiscolored {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3

    no dists
    no acOri
    
    #Color0 = 1
    #Color1 = 1
    nodeColors = Color0->(Node0 + Node1) + Color1->(Node3 + Node2 + Node4)
}

/* check {manyMiscolored => not noAdjColors[refs, nodeColors]} for 5 */

/* check {empty => oneColorPerNode[nodeColors]} */
/* check {single => oneColorPerNode[nodeColors]} */
/* check {twoSymmetric => oneColorPerNode[nodeColors]} */
/* check {twoDisconnected => oneColorPerNode[nodeColors]} */
/* check {symmetricMany => oneColorPerNode[nodeColors]} for 5 */

/* check {manyMiscolored => oneColorPerNode[nodeColors]} for 5 */

pred manyDuplicateNodeColor {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3

    no dists
    no acOri
    
    #Color0 = 1
    #Color1 = 1
    nodeColors = Color0->(Node0 + Node3 + Node1) +
        Color1->(Node1 + Node2 + Node4)
}

/* check {manyDuplicateNodeColor => not oneColorPerNode[nodeColors]} for 5 */

/* check {empty => validColoring[refs, nodeColors]} */
/* check {single => validColoring[refs, nodeColors]} */
/* check {twoSymmetric => validColoring[refs, nodeColors]} */
/* check {twoDisconnected => validColoring[refs, nodeColors]} */
/* check {symmetricMany => validColoring[refs, nodeColors]} for 5 */

/* check {empty => validKColoring[refs, nodeColors, 0]} */
/* check {single => validKColoring[refs, nodeColors, 1]} */
/* check {twoSymmetric => validKColoring[refs, nodeColors, 2]} */
/* check {twoDisconnected => validKColoring[refs, nodeColors, 1]} */
/* check {symmetricMany => validKColoring[refs, nodeColors, 2]} for 5 */

/* check {empty => validKColoring[refs, nodeColors, 2]} */
/* check {twoSymmetric => validKColoring[refs, nodeColors, 3]} */
/* check {twoDisconnected => validKColoring[refs, nodeColors, 2]} */
/* check {symmetricMany => validKColoring[refs, nodeColors, 3]} for 5 */

/* check {empty => not validKColoring[refs, nodeColors, -1]} */
/* check {twoSymmetric => not validKColoring[refs, nodeColors, 1]} */
/* check {twoDisconnected => not validKColoring[refs, nodeColors, 0]} */
/* check {symmetricMany => not validKColoring[refs, nodeColors, 1]} for 5 */


pred threeCompleteGraph {
    oneOfEach
    Node = Node0 + Node1 + Node2
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    refs = Node0->(Node1 + Node2) + Node1->(Node0 + Node2) +
        Node2->(Node0 + Node1)

    --no dists
    --no acOri
    
    #Color0 = 1
    #Color1 = 1
    #Color2 = 1
    #Color4 = 1
    nodeColors = Color0->Node0 + Color1->Node1 + Color2->Node2
}

pred fourSimpleCycle {

    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    refs = Node0->(Node1 + Node2) + Node1->(Node0 + Node3) +
        Node2->(Node0 + Node3) + Node3->(Node1 + Node2)

    --no dists
    --no acOri
    
    #Color0 = 1
    #Color1 = 1
    #Color2 = 1
    #Color3 = 1
    #Color4 = 1
    nodeColors = Color0->Node0 + Color1->Node1 + Color2->Node2 + Color3->Node3

}

pred fourCompleteGraph {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    refs = Node0->(Node1 + Node2 + Node3) + Node1->(Node0 + Node2 + Node3) +
        Node2->(Node0 + Node1 + Node3) + Node3->(Node0 + Node1 + Node2)

    --no dists
    --no acOri
    
    #Color0 = 1
    #Color1 = 1
    #Color2 = 1
    #Color4 = 1
    nodeColors = Color0->Node0 + Color1->Node1 + Color2->Node2 + Color4->Node3
}

/* check {threeCompleteGraph => validKColoring[refs, nodeColors, 3]} for 5 */
/* check {threeCompleteGraph => not validKColoring[refs, nodeColors, 2]} for 5 */

/* check {fourSimpleCycle => validKColoring[refs, nodeColors, 2]} for 5 */
/* check {fourSimpleCycle => not validKColoring[refs, nodeColors, 1]} for 5 */

/* check {fourCompleteGraph => validKColoring[refs, nodeColors, 4]} for 5 */
/* check {fourCompleteGraph => not validKColoring[refs, nodeColors, 3]} for 5 */

/* check {empty => kColorable[refs, 0]} for 5 Node, exactly 5 Color */
/* check {empty => kColorable[refs, 1]} for 5 Node, exactly 5 Color */
/* check {empty => kColorable[refs, 2]} for 5 Node, exactly 5 Color */


/* check {single => not kColorable[refs, 0]} for 5 Node, exactly 5 Color */
/* check {single => kColorable[refs, 1]} for 5 Node, exactly 5 Color */
/* check {single => kColorable[refs, 2]} for 5 Node, exactly 5 Color */

/* check {twoSymmetric => kColorable[refs, 2]} for 5 Node, exactly 5 Color */
/* check {twoSymmetric => kColorable[refs, 3]} for 5 Node, exactly 5 Color */
/* check {twoSymmetric => not kColorable[refs, 1]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {twoDisconnected} for 5 Node, exactly 5 Color */

/* check {twoDisconnected => kColorable[refs, 1]} for 5 Node, exactly 5 Color */
/* check {twoDisconnected => kColorable[refs, 2]} for 5 Node, exactly 5 Color */
/* check {twoDisconnected => not kColorable[refs, 0]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {symmetricMany} for 5 Node, exactly 5 Color */

/* check {symmetricMany => kColorable[refs, 2]} for 5 Node, exactly 5 Color */
/* check {symmetricMany => kColorable[refs, 3]} for 5 Node, exactly 5 Color */
/* check {symmetricMany => not kColorable[refs, 1]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {threeCompleteGraph} for 5 Node, exactly 5 Color */

/* check {threeCompleteGraph => kColorable[refs, 3]} for 5 Node, exactly 5 Color */
/* check {threeCompleteGraph => kColorable[refs, 4]} for 5 Node, exactly 5 Color */
/* check {threeCompleteGraph => not kColorable[refs, 2]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {fourSimpleCycle} for 5 Node, exactly 5 Color */

/* check {fourSimpleCycle => kColorable[refs, 2]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => kColorable[refs, 4]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => not kColorable[refs, 1]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {fourCompleteGraph} for 5 Node, exactly 5 Color */

/* check {fourCompleteGraph => kColorable[refs, 5]} for 5 Node, exactly 5 Color */
/* check {fourCompleteGraph => kColorable[refs, 4]} for 5 Node, exactly 5 Color */
/* check {fourCompleteGraph => not kColorable[refs, 3]} for 5 Node, exactly 5 Color */

/* check {threeCompleteGraph => isChromaticNumber[refs, 3]} for 5 Node, exactly 5 Color */
/* check {threeCompleteGraph => not isChromaticNumber[refs, 4]} for 5 Node, exactly 5 Color */
/* check {threeCompleteGraph => not isChromaticNumber[refs, 2]} for 5 Node, exactly 5 Color */

/* check {twoDisconnected => isChromaticNumber[refs, 1]} for 5 Node, exactly 5 Color */
/* check {symmetricMany => isChromaticNumber[refs, 2]} for 5 Node, exactly 5 Color */

/* check {fourSimpleCycle => isChromaticNumber[refs, 2]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => not isChromaticNumber[refs, 5]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => not isChromaticNumber[refs, 3]} for 5 Node, exactly 5 Color */

/* check {fourSimpleCycle => isChromaticNumber[refs, 4]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => not isChromaticNumber[refs, 5]} for 5 Node, exactly 5 Color */
/* check {fourSimpleCycle => not isChromaticNumber[refs, 3]} for 5 Node, exactly 5 Color */

pred symmetricManyNotLongestOrientation {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->1 + Node0->Node2->1 + Node2->Node0->1 +
        Node0->Node3->2 + Node3->Node0->2 + Node0->Node4->1 +
        Node4->Node0->1 + Node1->Node2->2 + Node2->Node1->2 +
        Node1->Node3->1 + Node3->Node1->1 + Node2->Node3->1 +
        Node3->Node2->1 + Node2->Node4->2 + Node4->Node2->2 +
        Node3->Node4->1 + Node4->Node3->1

    acOri = Node0->Node1 +  Node2->Node0 + Node3->Node2 +  Node3->Node4 +
         Node4->Node0 +  Node3->Node1
    
    no nodeColors
}

pred symmetricManyLongestOrientation {
    oneOfEach
    Node = Node0 + Node1 + Node2 + Node3 + Node4
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    #Node3 = 1
    #Node4 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0 +
        Node2->Node3 + Node3->Node2 + Node3->Node4 + Node4->Node3 +
        Node0->Node4 + Node4->Node0 + Node3->Node1 + Node1->Node3
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
        Node3->Node3->0 + Node4->Node4->0 + Node0->Node1->1 +
        Node1->Node0->-1 + Node0->Node2->-1 + Node2->Node0->1 +
        Node0->Node3->-1 + Node3->Node0->2 + Node0->Node4->-1 +
        Node4->Node0->1 + Node1->Node2->-1 + Node2->Node1->2 +
        Node1->Node3->-1 + Node3->Node1->1 + Node2->Node3->-1 +
        Node3->Node2->1 + Node2->Node4->-1 + Node4->Node2->-1 +
        Node3->Node4->1 + Node4->Node3->-1

    acOri = Node0->Node1 +  Node2->Node0 + Node3->Node2 +  Node3->Node4 +
         Node4->Node0 +  Node3->Node1
    
    no nodeColors
}

pred symmetricNotMinimum {
    oneOfEach
    Node = Node0 + Node1 + Node2
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
	Node0->Node1->1 + Node1->Node0->-1 + Node1->Node2->-1 + 
	Node2->Node1->2 + Node0->Node2->-1 + Node2->Node0->1

    acOri = Node0->Node1 +  Node2->Node0
    
    no nodeColors
}

pred minimumOrientation {
    oneOfEach
    Node = Node0 + Node1 + Node2
    #Node0 = 1
    #Node1 = 1
    #Node2 = 1
    refs = Node0->Node1 + Node1->Node0 + Node0->Node2 + Node2->Node0
    dists = Node0->Node0->0 + Node1->Node1->0 + Node2->Node2->0 +
	Node0->Node1->1 + Node1->Node0->-1 + Node1->Node2->-1 + 
	Node2->Node1->-1 + Node0->Node2->1 + Node2->Node0->-1

    acOri = Node0->Node1 +  Node0->Node2
    
    no nodeColors
}

/* check {empty => minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color */
/* check {twoSymmetric => minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color*/

/* check {symmetricMany => minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {symmetricManyNotLongestOrientation} for 5*/

// Verify some instance exists (some instance should exist)
/* run {minimumOrientation} for 5 */
/* check {minimumOrientation => minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color */

/* check {symmetricManyNotLongestOrientation => not minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color */

// Verify some instance exists (some instance should exist)
/* run {symmetricNotLongest} for 5 */
/* check {symmetricNotLongest => not minimalLongestLengthOrientation[refs, acOri, dists]} for 5 Node, exactly 5 Color */


pred setup {
    validSymmetric[refs]
    minimalLongestLengthOrientation[refs, acOri, dists]

    // avoid clutter
    no nodeColors
}

run setup for exactly 5 Node, exactly 5 Color

// only works for a non-empty graph
check {
    setup and #Node > 0 => isChromaticNumber[refs, add[longestPath[dists], 1]]
} for 5 Node, exactly 5 Color


-- vim: set filetype=forge tabstop=4 softtabstop=4 shiftwidth=4:
