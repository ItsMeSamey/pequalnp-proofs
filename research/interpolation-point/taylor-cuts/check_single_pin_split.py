"""Compare the analytic one-pin split table with direct selection enumeration."""
from itertools import combinations
from collections import Counter

def component(graph, initial, omit=0):
    reached = initial
    while True:
        new = reached
        for i, nbr in enumerate(graph):
            if reached >> i & 1:
                new |= nbr & ~omit
        if reached == new:
            return reached
        reached = new

def predicted(graph, T, p):
    bit = 1 << p
    k = int(bool(T & bit))
    table = {(k, 0)}
    U = T & ~bit
    if not k or component(graph,bit)&U:
        table.add((0,1))
    if U & ~graph[p] or component(graph,U,bit) & (graph[p]&~U):
        table.add((1-k,0))
    return table

def direct(graph,T,p):
    table=set()
    for s in range(1<<len(graph)):
        if not (s>>p&1):
            continue
        for b in (0,1):
            if all((s&j).bit_count()%2 == b*(T>>i&1)
                   for i,j in enumerate(graph) if s>>i&1):
                table.add(((s&T).bit_count()%2,b))
    return table

if __name__=='__main__':
    stats=Counter()
    for n in range(1,6):
        edges=list(combinations(range(n),2))
        for bits in range(1<<len(edges)):
            adj=[0]*n
            for i,(u,v) in enumerate(edges):
                if bits>>i&1:
                    adj[u]|=1<<v
                    adj[v]|=1<<u
            for T in range(1,1<<n):
                for p in range(n):
                    actual=direct(adj,T,p)
                    assert predicted(adj,T,p)==actual,(adj,T,p,actual)
                    stats[tuple(sorted(actual))]+=1
    print(sum(stats.values()),dict(stats))
