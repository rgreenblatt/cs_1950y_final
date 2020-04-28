sig Node {
    refs: set Node, -- undirected graph
    dists: set Node -> Int, -- distances from node to all other nodes
    acOri: set Node -- acyclic orientation for the graph
}

sig Color {
    nodeColors: set Node -- defines the color of each node
}

-- graph is undirected and irreflexive
pred defRefs[graph : Node -> Node] {
    ~graph in graph
    no iden & graph
}

pred empty {
    no Node
    no refs
    no dists
    no dists
    no acOri
}

/* check {empty => defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {empty} */

// Dirty hack to allow naming
sig Node0 extends Node {
}
sig Node1 extends Node {
}
sig Node2 extends Node {
}
sig Node3 extends Node {
}
sig Node4 extends Node {
}
sig Node5 extends Node {
}
sig Node6 extends Node {
}
sig Node7 extends Node {
}
sig Node8 extends Node {
}
sig Node9 extends Node {
}

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
}

pred single {
    oneOfEach
    Node = Node0
    #Node0 = 1
    no refs
    dists = Node0->Node0->0
    no acOri
}

/* check {single => defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {single} */

pred twoReflexive {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = Node0->Node1 + Node1->Node0
    dists = Node0->Node0->0 + Node1->Node1->0 + Node0->Node1->1 +
        Node1->Node0->1
    acOri = Node0->Node1
}

/* check {twoReflexive => defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {twoReflexive} */

pred twoOneDirection {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = Node0->Node1
    dists = Node0->Node0->0 + Node0->Node0->1 + Node0->Node1->1 +
        Node1->Node0->-1
    no acOri
}

/* check {twoOneDirection => not defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {twoOneDirection} */

pred mostlyReflexiveMany {
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

/* check {mostlyReflexiveMany => not defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {mostlyReflexiveMany} for 5 */

pred reflexiveMany {
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
         Node4->Node0 +  Node1->Node3
}

/* check {reflexiveMany => defRefs[refs]} */

// Verify some instance exists (some instance should exist)
/* run {reflexiveMany} for 5 */

-- each node has exactly one color
pred oneColorPerNode[coloring : Color -> Node] {
    all n : Node | one n.(~coloring)
}

// can be directed graph
/* fun getDists [graph : Node->Node] : Node->Node->Int { */
/*     all u : */ 
    
/* } */

-- defines distance metric for each node
pred defDists {
    all u : Node | all v : Node | {
        u = v => dists[u][v] = 0
        v in u.refs => dists[u][v] = 1
        (v not in u.(^refs)) and (not u = v) => dists[u][v] = -1
        ((v not in u.refs) and (not u = v) and (v in u.(^refs))) =>
            dists[u][v] = add[min[dists[u.refs][v]], 1]
    }
}

/* check {empty => defDists} */
/* check {single => defDists} */
/* check {twoReflexive => defDists} */
/* check {mostlyReflexiveMany => defDists} */
/* check {reflexiveMany => defDists} */

pred mostlyReflexiveManyWrongDist {
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

/* check {mostlyReflexiveManyWrongDist => not defDists} */

pred reflexiveManyWrongDist {
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

/* check {reflexiveManyWrongDist => not defDists} */

-- defines acOri as an acyclic orientation of the graph from refs
pred defOrientation {
    acOri in refs
    all u: Node | {
        -- acyclic
        u->u not in ^acOri
         -- exactly one direction picked for each edge
        all v : u.refs | (u->v in acOri iff v->u not in acOri)
    }
}

/* check {empty => defOrientation} */
/* check {single => defOrientation} */
/* check {twoReflexive => defOrientation} */
/* check {reflexiveMany => defOrientation} */

pred reflexiveManyInvalidOrientationDup {
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
/* run {reflexiveManyInvalidOrientationDup} for 5 */

/* check {reflexiveManyInvalidOrientationDup => not defOrientation} for 5 */

pred reflexiveManyInvalidOrientationMissing {
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
/* run {reflexiveManyInvalidOrientationMissing} for 5 */

/* check {reflexiveManyInvalidOrientationMissing => not defOrientation} for 5 */

-- ensures that no two adjacent nodes should have the same color
pred noAdjColors [graph : Node -> Node, coloring : Color -> Node]  {
    all n : Node | coloring.n not in coloring.(n.graph)
}

pred validColoring [graph : Node -> Node, coloring : Color -> Node] {
    noAdjColors[graph, coloring]
    oneColorPerNode[coloring]
}

pred validKColoring [graph : Node -> Node, coloring : Color -> Node, k : Int] {
    validColoring[graph, coloring]
    #(coloring.Node) <= k // number of "used" colors is k or lower
}

pred kColorable [graph : Node -> Node, k : Int] {
    some coloring : Color->Node | validKColoring[graph, coloring, k]
}

pred isChromaticNumber [graph : Node->Node, k : Int] {
    kColorable[graph, k]
    no smaller : Int | smaller < k and kColorable[graph, smaller]
}

/* pred longestPathLength [graph : Node -> Node, len : Int] { */
/*     some path : set Node when valid */
    
/* } */

/* pred someColoring { */
/*     defRefs[refs] */
/*     validColoring[refs, nodeColors] */
/* } */

/* run {someColoring} for exactly 4 Node, exactly 2 Color */

/* pred notThreeColorable { */
/*     defRefs[refs] */
/*     not kColorable[refs, 3] */
/*     no dists */
/*     no acOri */
/*     no nodeColors */
/* } */

/* run {notThreeColorable} for exactly 4 Node, exactly 3 Color */

pred graphChromaticNumberThree {
    defRefs[refs]
    isChromaticNumber[refs, 3]
}

run {graphChromaticNumberThree} for exactly 4 Node, exactly 4 Color

-- vim: set filetype=forge tabstop=4 softtabstop=4 shiftwidth=4:
