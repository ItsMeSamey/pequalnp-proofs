"""Compare two-hole profiles and original IDs with exhaustive matching enumeration."""
from itertools import combinations,product
from random import Random


def enumerate_ids(vertices, edges):
    if not vertices:
        yield ()
        return
    u=min(vertices)
    for i,(a,b,g) in enumerate(edges):
        if u in (a,b) and {a,b}<=vertices:
            for rest in enumerate_ids(vertices-{a,b},edges):
                yield (i,)+rest


def expected(vertices,edges,width):
    out={}
    for ids in enumerate_ids(set(vertices),edges):
        g=tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(width))
        out.setdefault(g,set()).add(frozenset(ids))
    return out


def fixtures():
    for labels in product(range(3),repeat=6):
        edges=[(u,v,(t,)) for (u,v),t in zip(combinations(range(4),2),labels)]
        if len(expected(range(4),edges,1))==1:
            yield 4,edges,1
    rng=Random(2881)
    for _ in range(6):
        p=[[rng.randrange(3) for _ in range(2)] for _ in range(6)]
        yield 6,[(u,v,tuple((a+b)%3 for a,b in zip(p[u],p[v])))
                 for u,v in combinations(range(6),2)],2
    yield 8,[(u,v,((v%3 if u==0 else 0),)) for u,v in combinations(range(5),2)]+[
        (0,5,(0,)),(5,6,(0,)),(5,7,(0,)),(6,7,(0,))],1
    yield 6,[(0,1,(0,)),(0,1,(1,)),(1,2,(0,)),(2,0,(2,)),(3,4,(0,)),
             (4,5,(1,)),(5,3,(2,)),(0,3,(1,))],1


def main():
    from labelled_neutral_two_holes import solve
    calls=0
    for n,edges,width in fixtures():
        for a,b in combinations(range(n),2):
            by_gain=expected(set(range(n))-{a,b},edges,width)
            for t in product(range(3),repeat=width):
                status,w,stats=solve(n,edges,(a,b),t)
                assert status==("SAT" if t in by_gain else "UNSAT"), (edges,(a,b),t,stats)
                if w is not None:
                    assert len(w)==n//2-1 and frozenset(w) in by_gain[t]
                calls+=1
    n, bicycle, width=list(fixtures())[-1]
    assert len(expected(set(range(n))-{2,5},bicycle,width))==2
    bad=[(u,v,(int((u,v)==(0,1)),)) for u,v in combinations(range(4),2)]
    try:
        solve(4,bad,(0,1),(0,),audit_neutral=True)
    except ValueError:
        pass
    else:
        raise AssertionError("neutrality audit accepted unpromised K4")
    print(calls,"original-ID neutral checks plus strict mixed bicycle and unpromised K4")


if __name__=="__main__":
    main()
