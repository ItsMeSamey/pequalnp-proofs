"""Trace the paired diagnostic construction directly, using distinct sockets per occurrence."""
from itertools import combinations, product
from strict_forest_reference import physical

def build(clauses):
    n=max(max(c) for c in clauses)+1
    chunks=[[] for _ in range(n)]
    gates=[]
    nxt=2
    diagnostics=[]
    for clause in clauses:
        sites=[]
        for v in clause:
            chunks[v].extend((nxt,nxt+1))
            sites.append(nxt)
            nxt+=2
        a,b,c=sites
        diagnostics.extend(((a,b,c),(a+1,c+1,b+1)))
    rails=[[0],[1]]
    for ch in chunks:
        a,b,c=range(nxt,nxt+3)
        nxt+=3
        rails[0].extend([a]+ch+[b])
        rails[1].append(c)
        gates.append((a,b,c))
    p=list(range(nxt))
    for rail in rails:
        for i,v in enumerate(rail):
            p[v]=rail[(i+1)%len(rail)]
    return p,gates,diagnostics

def joins(p):
    x=p[0]
    while x not in (0,1):
        x=p[x]
    return x==1

def check(clauses,full):
    p,g,d=build(clauses)
    for x in product(range(2),repeat=len(g)):
        base=physical(p,g,x)
        assert not joins(base)
        for j,clause in enumerate(clauses):
            mixed=len({x[v] for v in clause})>1
            count=sum(joins(physical(base,[gate],[1])) for gate in d[2*j:2*j+2])
            assert count==mixed
        if full:
            possible=any(joins(physical(base,d,y)) for y in product(range(2),repeat=len(d)))
            assert possible==any(len({x[v] for v in c})>1 for c in clauses)

if __name__=='__main__':
    check([(0,0,0),(0,0,1),(1,2,1),(2,2,2)],True)
    check(list(combinations(range(5),3)),False)
    print('All 40 base masks agree, including repeated occurrences and all ten triples of K5.')
