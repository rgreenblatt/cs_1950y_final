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
        ((v not in u.refs) and (not u = v) and (v in u.(^refs))) => dists[u][v] = add[min[dists[u.refs][v]], 1]
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
