"""Bounded independent raw-clause private-block oracle and exact dimer controls."""
from itertools import combinations
from fractions import Fraction
from random import Random
from padded_planar_solver import count,_matching_sum


def build(edges,extra=0):
    base=max(max(e) for e in edges)
    end=base
    blocks=[]
    rows=[]
    for i,(u,v) in enumerate(edges):
        b=2+i%2
        for sign in (-1,1):
            z=end+1
            private=tuple(range(z,z+b+1))
            end+=b+1
            block=[(sign*u,sign*v,z)]+[tuple(-k for k in t) for t in combinations(private,3)]
            rows.extend(block)
            blocks.append((private,block))
    return end+extra,base,blocks,rows


def original(n,base,blocks):
    # For fixed base spins enumerate each disjoint raw block and replay every clause.
    total=0
    for x in range(1<<base):
        ways=1
        for private,rows in blocks:
            cnt=0
            for a in range(1<<len(private)):
                word=x|sum(((a>>i)&1)<<(v-1) for i,v in enumerate(private))
                cnt+=all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in row) for row in rows)
            ways*=cnt
        total+=ways
    return total<<(n-base-sum(len(p) for p,_ in blocks))


def dimers(G,remaining):
    if not remaining:
        return Fraction(1)
    u=min(remaining)
    return sum(G[u][v]['weight']*dimers(G,remaining-{u,v}) for v in G[u] if v in remaining)


if __name__=='__main__':
    import networkx as nx
    rng=Random(779)
    triangle=[(1,2),(2,3),(1,3)]
    barbell=triangle+[(3,4),(4,5),(5,6),(4,6)]
    for E in [triangle,barbell,[(1,2),(2,3),(3,4),(4,1),(1,3)],list(combinations(range(1,5),2))]:
        n,base,blocks,rows=build(E,2)
        expected=original(n,base,blocks)
        perm=list(range(1,n+1))
        rng.shuffle(perm)
        renamed=[tuple((1 if l>0 else -1)*perm[abs(l)-1] for l in row) for row in rows]
        rng.shuffle(renamed)
        assert count(n,renamed)==expected
    n,_,_,rows=build(triangle)
    assert count(n,rows[:-1]) is None and count(n,rows+[rows[0]]) is None
    n,_,_,rows=build([(i,j) for i in (1,2,3) for j in (4,5,6)])
    assert count(n,rows) is None
    n,_,_,rows=build(triangle+[(4,5),(5,6),(4,6)])
    assert count(n,rows) is None
    for G in [nx.path_graph(6),nx.cycle_graph(6),nx.complete_graph(4),nx.circular_ladder_graph(4)]:
        for u,v in G.edges:
            G[u][v]['weight']=Fraction(rng.randrange(1,9),rng.randrange(1,7))
        assert _matching_sum(G,nx)==dimers(G,set(G))
    print('4 relabeled original padded CNFs including bridge/unused bits, 4 rejection controls, 4 exact weighted planar dimer checks')
