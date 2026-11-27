"""Compare quotient matching witnesses with direct enumeration of socket permutations."""
from itertools import combinations, permutations
from random import Random
import networkx as nx

def labels(p):
    owner={}
    for s in range(len(p)):
        v=s
        while v not in owner:
            owner[v]=s
            v=p[v]
    return owner

def enumerate_matchings(edges,used=frozenset()):
    if not edges:
        yield []
        return
    edge=edges[0]
    yield from enumerate_matchings(edges[1:],used)
    if used.isdisjoint(edge):
        for suffix in enumerate_matchings(edges[1:],used.union(edge)):
            yield [edge]+suffix

def physical(p,edges):
    q=list(p)
    for s,t in edges:q[s],q[t]=q[t],q[s]
    return labels(q)

def solve(p,edges,s,t):
    owner=labels(p)
    u,v=owner[s],owner[t]
    if u==v:return []
    n=len(p)
    graph=nx.Graph()
    graph.add_edges_from((i,n+i) for i in range(n))
    graph.add_edges_from(edges)
    graph.add_edges_from((n+i,n+j) for i,j in combinations(range(n),2) if owner[i]==owner[j])
    a,b=2*n,2*n+1
    graph.add_edges_from((a,n+i) for i in range(n) if owner[i]==u)
    graph.add_edges_from((b,n+i) for i in range(n) if owner[i]==v)
    perfect=nx.max_weight_matching(graph,maxcardinality=True)
    if len(perfect)!=n+1:return None
    partner=dict(perfect)
    partner.update((j,i) for i,j in perfect)
    quotient=nx.Graph()
    i=partner[a]
    while i!=b:
        x=i-n
        y=partner[x]
        quotient.add_edge(owner[x],owner[y],pair=(x,y))
        i=partner[y+n]
    path=nx.shortest_path(quotient,u,v)
    return [quotient[x][y]['pair'] for x,y in zip(path,path[1:])]

if __name__=='__main__':
    rng=Random(272)
    total=yes=0
    for n in (3,4,5,6):
        pairs=list(combinations(range(n),2))
        cases=([(p,[e for j,e in enumerate(pairs) if mask>>j&1]) for p in permutations(range(n)) for mask in range(1<<len(pairs))] if n<=4 else [(rng.sample(range(n),n),rng.sample(pairs,rng.randrange(len(pairs)+1))) for _ in range(150)])
        for p,edges in cases:
            states=[physical(p,m) for m in enumerate_matchings(edges)]
            for s,t in pairs:
                m=solve(p,edges,s,t)
                truth=any(d[s]==d[t] for d in states)
                if truth!=(m is not None) or (truth and physical(p,m)[s]!=physical(p,m)[t]):raise AssertionError((p,edges,s,t,m))
                total+=1;yes+=truth
    print(total,'queries;',yes,'witnesses')
