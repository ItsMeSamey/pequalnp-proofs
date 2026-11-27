"""Exhaustive free rotations, with a fixed hub rotation and marked inserted edge."""
from itertools import combinations_with_replacement, permutations, product
from random import Random
import networkx as nx


def trial(edges, hub_order, u, v):
    g = nx.MultiGraph()
    darts = {i: [] for e in edges for i in e}
    for i, (x, y) in enumerate(edges):
        g.add_edge(x, y, key=i)
        darts[x].append(2*i)
        darts[y].append(2*i+1)
    blocks = g.copy()
    blocks.remove_edges_from(list(nx.bridges(g)))
    parts = list(nx.connected_components(blocks))
    index = {v: i for i, part in enumerate(parts) for v in part}
    tree = nx.Graph()
    tree.add_nodes_from(range(len(parts)))
    tree.add_edges_from((index[x],index[y]) for x,y in nx.bridges(g))
    pred = any(blocks.subgraph(parts[j]).number_of_edges() for j in nx.shortest_path(tree,index[u],index[v]))
    first = 2*len(edges)
    darts[u].append(first)
    darts[v].append(first+1)
    darts[0] = list(hub_order)
    flex = [a for x,a in darts.items() if x and len(a)==3]
    for signs in product((0,1),repeat=len(flex)):
        succ = {}
        for a in darts.values():
            for j,h in enumerate(a):
                succ[h] = a[(j+1)%len(a)]
        for a,reverse in zip(flex,signs):
            if reverse:
                for j,h in enumerate(a):
                    succ[h] = a[j-1]
        h = succ[first^1]
        while h not in (first, first+1):
            h = succ[h^1]
        if h == first+1:
            return pred, True
    return pred, False


if __name__ == '__main__':
    rng = Random(58123)
    tests=0
    for n in range(2,8):
        for _ in range(400):
            vs=list(range(1,n))
            edges=[(i,rng.randrange(1,i)) for i in range(2,n)]
            edges.append((0,rng.choice(vs)))
            for _ in range(rng.randrange(8)):
                edges.append((rng.randrange(n),rng.randrange(n)))
            degree=[sum(e.count(v) for e in edges) for v in range(n)]
            if max(degree[1:])>3:continue
            hub=[2*i+j for i,e in enumerate(edges) for j,x in enumerate(e) if not x]
            rng.shuffle(hub)
            for u,v in combinations_with_replacement(vs,2):
                if degree[u]+1+(u==v)>3 or degree[v]>2:continue
                p,a=trial(edges,hub,u,v)
                tests+=1
                if p!=a:
                    print('COUNTEREXAMPLE',edges,hub,u,v,p,a)
                    raise SystemExit(1)
    print(tests,'queries passed')
