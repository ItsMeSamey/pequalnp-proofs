"""Exhaust all simple graphs and affine flats through four variables."""
from itertools import combinations


def rank(rows):
    pivots={}
    for u in rows:
        while u:
            j=u.bit_length()
            if j not in pivots:
                pivots[j]=u
                break
            u^=pivots[j]
    return len(pivots)


def flats(q,t):
    seen=set()
    for base in combinations(range(1,1<<q),t):
        if rank(base)!=t:continue
        grid=[0]
        for b in base:grid.extend([u^b for u in grid])
        for offset in range(1<<q):
            points=[u^offset for u in grid]
            key=tuple(sorted(points))
            if key not in seen:
                seen.add(key)
                yield points


def quadratic_part(points,edge):
    values=[int(x&edge==edge) for x in points]
    t=(len(values)-1).bit_length()
    for j in range(t):
        for x in range(len(values)):
            if x>>j&1:values[x]^=values[x^(1<<j)]
    assert all(not b or x.bit_count()<=2 for x,b in enumerate(values))
    return sum(b<<x for x,b in enumerate(values) if x.bit_count()==2)


def check(q):
    edges=[(1<<a)|(1<<b) for a,b in combinations(range(q),2)]
    counts=[]
    for t in range(q+1):
        spaces=list(flats(q,t))
        rows=[[quadratic_part(xs,e) for e in edges] for xs in spaces]
        coordinate=[sum(1<<j for j in J) for J in combinations(range(q),t)]
        for g in range(1<<len(edges)):
            actual=min(rank(v for i,v in enumerate(row) if g>>i&1) for row in rows)
            target=min(sum(e&c==e for i,e in enumerate(edges) if g>>i&1) for c in coordinate)
            assert actual==target
        counts.append(len(spaces))
    print(q,1<<len(edges),'graphs, flat counts',counts)


if __name__=='__main__':
    for q in range(1,5):check(q)
    # K3 on the noncoordinate even-parity plane: its three products
    # all have the same nonzero quadratic part, attaining the minimum one.
    xs=[0,3,5,6]
    parts=[quadratic_part(xs,e) for e in (3,5,6)]
    assert len(set(parts))==1 and rank(parts)==1
