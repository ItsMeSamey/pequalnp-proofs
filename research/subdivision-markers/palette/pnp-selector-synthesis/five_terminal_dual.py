"""Exact indexed W generators from a witness-producing first-space solver."""
from itertools import combinations
from planar_moment_certificate import CertifiedDual


def component_lifts(vertices,edges,charge,first_space):
    root=vertices[0]
    adj={v:[] for v in vertices}
    for i,(u,v) in enumerate(edges):
        adj[u].append((v,i));adj[v].append((u,i))
    parent={root:(None,None)};order=[root]
    for u in order:
        for v,i in adj[u]:
            if v not in parent:
                parent[v]=(u,i);order.append(v)
    tree={i for _,i in parent.values() if i is not None}
    path={root:0}
    for v in order[1:]:
        u,i=parent[v]
        path[v]=path[u]^(1<<i)
    keys=[0]*len(edges);row=1
    for i,(u,v) in enumerate(edges):
        if i in tree:
            continue
        cycle=(1<<i)^path[u]^path[v]
        while cycle:
            bit=cycle&-cycle
            keys[bit.bit_length()-1]|=row
            cycle^=bit
        row<<=1
    totals={v:charge[v] for v in vertices};tags=[0]*len(edges)
    for v in reversed(order[1:]):
        u,i=parent[v]
        tags[i]=totals[v];totals[u]^=tags[i]
    if totals[root]:
        raise ValueError("nonzero component charge")
    yield sum(1<<v for v in vertices)
    if edges:
        for word in first_space(keys,tags):
            labels=sum((((path[v]&word).bit_count()%2)<<v) for v in vertices)
            actual=sum(((((labels>>u)^(labels>>v))&1)<<i) for i,(u,v) in enumerate(edges))
            if actual!=word:
                raise ValueError("first-space witness is not a cut")
            yield labels


def terminal_path_packing(dual):
    """Gallai path packing via one maximum matching after duplicating neutral vertices."""
    import networkx as nx
    graph=nx.Graph()
    copies=[]
    for i,charge in enumerate(dual.charge):
        group=(2*i,) if charge else (2*i,2*i+1)
        copies.append(group)
        graph.add_nodes_from(group)
        if not charge:
            graph.add_edge(*group)
    for u,v,_ in dual.edges:
        if u!=v:
            graph.add_edges_from((a,b) for a in copies[u] for b in copies[v])
    matching=nx.max_weight_matching(graph,maxcardinality=True)
    return len(matching)-(len(copies)-len(dual.terminals))


def generators(n,edges,first_space):
    dual=CertifiedDual(n,edges)
    if len(dual.terminals)>5 and terminal_path_packing(dual)>2:
        raise ValueError("two-anchor packing condition not certified")
    if not dual.terminals:
        return ((dual.cut(1<<u),dual.cut(1<<v)) for u,v in combinations(range(n-1),2))
    return neutral_generators(dual,first_space)


def neutral_generators(dual,first_space):
    """Baseline W0, valid with any terminal count."""
    n=len(dual.graph)
    for z,q in enumerate(dual.charge):
        if q or not dual.compatible(1<<z,0):
            continue
        seen={z}
        for root in range(n):
            if root in seen:
                continue
            vertices=[root];seen.add(root);ids=set()
            for u in vertices:
                for v,i in dual.graph[u]:
                    if v!=z:
                        ids.add(i)
                        if v not in seen:
                            seen.add(v);vertices.append(v)
            subedges=[dual.edges[i][:2] for i in sorted(ids)]
            for x in component_lifts(vertices,subedges,dual.charge,first_space):
                if not dual.compatible(1<<z,x):
                    raise ValueError("invalid physical paired witness")
                a,b=dual.cut(1<<z),dual.cut(x)
                if a and b and a!=b:
                    yield a,b
