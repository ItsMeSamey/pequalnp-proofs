"""Ordinary four-cycle multiplicity and raw induced all-odd supports."""
from itertools import combinations
from random import Random


def graph(n, edges):
    rows = [0]*n
    for i,j in edges:
        rows[i] |= 1<<j
        rows[j] |= 1<<i
    return rows


def multiplicities(rows):
    # An edge ij lies on one cycle per length-three simple alternate i-j path.
    return {(i,j):sum((rows[k] & rows[j] & ~(1<<i)).bit_count()
                      for k in range(len(rows)) if k!=j and rows[i]>>k&1)
            for i,j in combinations(range(len(rows)),2) if rows[i]>>j&1}


def supports(rows, required=0):
    free = ((1<<len(rows))-1) ^ required
    t = free
    while True:
        s = required | t
        if s.bit_count()%2==0 and all((s&r).bit_count()%2 for i,r in enumerate(rows) if s>>i&1):
            yield s
        if not t:
            return
        t = (t-1)&free


def check_bounds(rows):
    maximum = max(multiplicities(rows).values(),default=0)
    if maximum>1:
        return 0,0
    cap = 8 if maximum else 6
    shortest = {}
    for s in supports(rows):
        for pair in combinations((i for i in range(len(rows)) if s>>i&1),2):
            shortest[pair]=min(shortest.get(pair,len(rows)+1),s.bit_count())
    assert all(k<=cap for k in shortest.values())
    return 1,len(rows)*(len(rows)-1)//2


def main():
    import networkx as nx
    atlas_graphs = atlas_pairs = 0
    for g in nx.graph_atlas_g():
        count,pairs=check_bounds(graph(len(g),g.edges()))
        atlas_graphs+=count
        atlas_pairs+=pairs
    corona=graph(8,[(i,(i+1)%4) for i in range(4)]+[(i,i+4) for i in range(4)])
    assert max(multiplicities(corona).values())==1
    assert list(supports(corona,(1<<4)|(1<<5)))==[255]
    assert set(multiplicities(graph(4,combinations(range(4),2))).values())=={2}
    rows=graph(4,[(0,2),(1,3)])
    p,q=0,1
    relay=[]
    for round_index in range(8):
        n=len(rows)
        assert list(supports(rows,(1<<p)|(1<<q)))==[(1<<n)-1]
        vals=multiplicities(rows).values()
        assert max(vals,default=0)<=2 and sum(vals)//4==max(0,round_index-1)
        relay.append((n,sum(vals)//4,max(vals,default=0)))
        assert not (rows[p]>>q&1)
        rows[p]|=1<<q|1<<n
        rows[q]|=1<<p|1<<(n+1)
        rows.extend((1<<p,1<<q))
        p,q=n,n+1
    rng=Random(194005)
    square_count=0
    for _ in range(160):
        n=rng.randrange(8,13)
        edges=list(combinations(range(n),2))
        rng.shuffle(edges)
        retained=[]
        for e in edges[:rng.randint(n,2*n)]:
            trial=graph(n,retained+[e])
            if max(multiplicities(trial).values())<=1:
                retained.append(e)
        r=graph(n,retained)
        assert check_bounds(r)[0]
        square_count+=bool(max(multiplicities(r).values()))
    print('atlas class graphs/pairs',atlas_graphs,atlas_pairs,'seeded',160,'with squares',square_count)
    print('relay (sites, ordinary squares, max per edge)',relay)


if __name__=='__main__':
    main()
