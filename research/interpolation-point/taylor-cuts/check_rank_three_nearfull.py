"""Check the exceptional-cell catalog, including every six-singleton simple graph."""
from itertools import combinations
from collections import Counter

def dot(u,v):
    return (u&v).bit_count()%2

def response(graph,labels):
    out=set()
    for s in range(1<<len(graph)):
        c=0
        for i,u in enumerate(labels):
            if s>>i&1: c^=u
        if c!=7:continue
        for b in (0,3,5,6):
            if all(not(s>>i&1) or dot(graph[i],s)==dot(b,u) for i,u in enumerate(labels)):
                out.add(b)
    return out

if __name__=='__main__':
    labels=list(range(1,7))
    pairs=list(combinations(range(6),2))
    all_in={0,3,5,6}
    counts=Counter()
    for mask in range(1<<len(pairs)):
        graph=[0]*6
        for i,(v,w) in enumerate(pairs):
            if mask>>i&1:
                graph[v]|=1<<w
                graph[w]|=1<<v
        out=response(graph,labels)
        potential={b for b in all_in if all(dot(b,u)!=((graph[u-1]>>(6-u))&1) for u in (1,2,3))}
        assert len(potential)<=1 and (all_in-out)<=potential
        counts[tuple(sorted(all_in-out))]+=1
    print(counts)
    graph=[0]*6
    for u,v in [(1,2),(1,3),(1,6),(2,3),(2,5),(3,4),(4,5)]:
        graph[u-1]|=1<<(v-1);graph[v-1]|=1<<(u-1)
    assert all_in-response(graph,labels)=={0}
