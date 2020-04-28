sig Node {
    refs: set Node, -- undirected graph
    dists: set Node -> Int, -- distances from node to all other nodes
    acOri: set Node -- acyclic orientation for the graph
}

sig Color {
    nodeColors: set Node -- defines the color of each node
}

-- refs is undirected and irreflexive
pred defRefs {
    ~refs in refs
    no iden & refs
}

pred Empty {
    no Node
    no refs
    no dists
    no dists
    no acOri
}

/* check {Empty => defRefs} */

// Verify some instance exists (some instance should exist)
/* run {Empty} */

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

/* check {single => defRefs} */ 

// Verify some instance exists (some instance should exist)
/* run {single} */

pred twoReflexive {
    oneOfEach
    Node = Node0 + Node1
    #Node0 = 1
    #Node1 = 1
    refs = Node0->Node1 + Node1->Node0
    dists = Node0->Node0->0 + Node0->Node1->1 + Node1->Node0->1
    no acOri
}

/* check {twoReflexive => defRefs} */

// Verify some instance exists (some instance should exist)
/* run {twoReflexive} */

-- each node has exactly one color
pred oneColorPerNode {
    all n : Node | one n.(~nodeColors)
}
-- defines distance metric for each node
pred defDists {
    all u : Node | all v : Node | {
        u = v => dists[u][v] = 0
        v in u.refs => dists[u][v] = 1
        v not in u.(^refs) => dists[u][v] = -1
        ((v not in u.refs) and (not u = v) and (v in u.(^refs))) =>
            dists[u][v] = add[min[dists[u.refs][v]], 1]
    }
}

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

-- ensures that no two adjacent nodes should have the same color
pred noAdjColors {
    all n : Node | nodeColors.n not in nodeColors.(n.refs)
}

pred setup {
    defRefs
    oneColorPerNode
    defDists
    defOrientation
    noAdjColors
}

run {setup} for exactly 4 Node, exactly 2 Color

-- vim: set filetype=forge tabstop=4 softtabstop=4 shiftwidth=4:
