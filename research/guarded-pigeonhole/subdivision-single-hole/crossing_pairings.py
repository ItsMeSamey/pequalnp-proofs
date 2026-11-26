"""Extract two distinct boundary pairings from a cubic bipartite two-star cap."""
from itertools import combinations,permutations,product
from random import Random
import networkx as nx


def perfect(left,right,edges,available,forced=()):
    matched=set(forced)
    used_a={edges[e][0] for e in forced}
    used_b={edges[e][1] for e in forced}
    if len(used_a)!=len(forced) or len(used_b)!=len(forced):return None
    G=nx.Graph()
    A={(0,a) for a in left-used_a}
    B={(1,b) for b in right-used_b}
    G.add_nodes_from(A|B)
    for e in sorted(available):
        a,b=edges[e]
        if a not in used_a and b not in used_b:G.add_edge((0,a),(1,b),edge=e)
    M=nx.bipartite.maximum_matching(G,top_nodes=A)
    if len(M)!=len(A)+len(B):return None
    matched.update(G[a][M[a]]['edge'] for a in A)
    return matched


def two_pairings(edges,u,w):
    """Edges are indexed ordered (left,right) pairs, vertices u,w on the right."""
    A,B=map(set,zip(*edges))
    U=[i for i,(_,v) in enumerate(edges) if v==u]
    W=[i for i,(_,v) in enumerate(edges) if v==w]
    if u==w or len(U)!=3 or len(W)!=3:raise ValueError('distinct cubic root vertices required')
    if any(sum(a==x for a,b in edges)!=3 for x in A) or any(sum(b==y for a,b in edges)!=3 for y in B):
        raise ValueError('expected cubic bipartite multigraph')
    all_edges=set(range(len(edges)))
    found={}
    for e,f in product(U,W):
        red=perfect(A,B,edges,all_edges,(e,f))
        if red is None:continue
        green=perfect(A,B,edges,all_edges-red)
        blue=all_edges-red-green
        groups=[red,green,blue]
        groups.sort(key=lambda S:next(i for i,k in enumerate(U) if k in S))
        colors=[next(i for i,S in enumerate(groups) if j in S) for j in range(len(edges))]
        assert all({colors[j] for j,(a,b) in enumerate(edges) if a==v}=={0,1,2} for v in A)
        assert all({colors[j] for j,(a,b) in enumerate(edges) if b==v}=={0,1,2} for v in B)
        found[tuple(colors[f] for f in W)]=colors
        if len(found)>=2:return found
    raise AssertionError('unique crossing signature in cubic bipartite cap')


if __name__=='__main__':
    K=list(product(range(3),repeat=2))
    got=two_pairings(K,0,1)
    assert set(got)=={(1,2,0),(2,0,1)}
    rng=Random(892)
    for _ in range(400):
        n=rng.randrange(2,24)
        edges=[]
        for j in range(3):edges.extend(enumerate(rng.sample(range(n),n)))
        roots=rng.sample(range(n),2)
        assert len(two_pairings(edges,*roots))==2
    print('K3,3 sharp signature and two verified colorings on 400 random cubic bipartite multigraphs.')
