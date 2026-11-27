"""Decision via branching on high-degree vertices of the peeled 3-core."""
from itertools import permutations,product
import networkx as nx


def _degree_lists(component,domain):
    blocks=[set(b) for b in nx.biconnected_components(component)]
    if not blocks:
        return all(domain[v] for v in component)
    for block in blocks:
        sub=component.subgraph(block)
        if sub.number_of_edges()==len(block)*(len(block)-1)//2:
            continue
        if len(block)%2==1 and all(d==2 for _,d in sub.degree):
            continue
        # A non-Gallai component is degree-choosable.
        return True
    tree=nx.Graph()
    for i,block in enumerate(blocks):
        for v in block:
            tree.add_edge(('b',i),('v',v))
    root=('v',next(iter(component)))
    parent={root:None}
    order=[root]
    for u in order:
        for v in tree[u]:
            if v!=parent[u]:
                parent[v]=u
                order.append(v)
    allowed={}
    for u in reversed(order):
        tag,i=u
        if tag=='v':
            colors=set(domain[i])
            for b in tree[u]:
                if b!=parent[u]:
                    colors &= allowed[b]
            allowed[u]=colors
            continue
        block=blocks[i]
        v=parent[u][1]
        sub=component.subgraph(block)
        if sub.number_of_edges()==len(block)*(len(block)-1)//2:
            seq=[v,*sorted(block-{v})]
            allowed[u]={cols[0] for cols in permutations(range(3),len(seq))
                        if all(c in allowed['v',w] for c,w in zip(cols[1:],seq[1:]))}
        else:
            seq=[v,next(iter(sub[v]))]
            while len(seq)<len(block):
                seq.append(next(w for w in sub[seq[-1]] if w!=seq[-2]))
            colors=set()
            for anchor in range(3):
                reach={anchor}
                for w in seq[1:]:
                    reach={c for c in allowed['v',w] if any(c!=d for d in reach)}
                if reach-{anchor}:
                    colors.add(anchor)
            allowed[u]=colors
    return bool(allowed[root])


def decide(graph):
    if graph.is_directed() or graph.is_multigraph():
        raise ValueError("expected a simple undirected graph")
    if nx.number_of_selfloops(graph):
        return False
    core=nx.k_core(graph,k=3)
    for cc in nx.connected_components(core):
        local=core.subgraph(cc)
        high=[v for v,d in local.degree() if d>=4]
        low=local.subgraph(set(local)-set(high))
        for word in product(range(3),repeat=len(high)):
            fixed=dict(zip(high,word))
            if any(fixed[u]==fixed[v] for u,v in local.subgraph(high).edges):
                continue
            domain={v:set(range(3))-{fixed[u] for u in local[v] if u in fixed} for v in low}
            if all(_degree_lists(low.subgraph(b),domain) for b in nx.connected_components(low)):
                break
        else:
            return False
    return True
