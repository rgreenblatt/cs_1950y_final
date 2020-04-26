#lang forge

sig Node {
    refs: set Node,
    dists: set Node -> Int
}

sig Color {
    nodeColors: set Node
}

-- graph is undirected
pred symmetric {
    ~refs in refs
}

-- graph is irreflexive
pred irreflexive {
    no iden & refs
}

-- each node has exactly one color
pred oneColor {
    all n : Node | one n.(~nodeColors)
}

pred defDists {
    all u : Node | all v : Node | {
        u = v => dists[u][v] = sing[0]
        v in u.refs => dists[u][v] = sing[1]
        v not in u.(^refs) => dists[u][v] = sing[-1]
        ((v not in u.refs) and (not u = v) and (v in u.(^refs))) => dists[u][v] = sing[add[min[dists[u.refs][v]], 1]]
    }
}

pred setup {
    symmetric
    irreflexive
    oneColor
    defDists
}

run {setup} for exactly 4 Node, exactly 1 Color