from itertools import combinations
from time import monotonic
from modal_fibers import solve_auto,build


def instance(v):
    vertices=[(p,i) for p in map(frozenset,combinations(range(v),2)) for i in range(5)]
    edges=[(x,y) for x,y in combinations(range(len(vertices)),2)
           if vertices[x][0].isdisjoint(vertices[y][0]) and vertices[x][1]!=vertices[y][1]]
    return build(len(vertices),edges)


for v,expected in ((6,'SAT'),(7,'UNSAT')):
    raw=instance(v)
    assert solve_auto(raw,max_assignments=1)[0]=='UNKNOWN'
    start=monotonic()
    status,word=solve_auto(raw,max_assignments=50000)
    assert status==expected
    if word is not None:assert len(word)<=4*(5*v*(v-1)//2)
    print(v,status,'word',len(word or ''),'seconds',round(monotonic()-start,3))
