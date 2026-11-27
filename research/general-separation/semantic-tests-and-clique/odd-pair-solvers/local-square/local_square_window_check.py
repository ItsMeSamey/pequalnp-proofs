"""Raw parity, recognition and witness checks for the local-square window search."""
from itertools import combinations
from local_square_window_solver import fold,recognize,repair,solve
from odd_pair_square_multiplicity_check import graph,multiplicities,supports
from quartic_window_check import physical_walk


def direct_recognition(rows):
    counts=multiplicities(rows)
    high=[v for v,r in enumerate(rows) if r.bit_count()>4]
    for v in high:
        nbr=[i for i,r in enumerate(rows) if r>>v&1]
        if any(rows[i]>>j&1 for i,j in combinations(nbr,2)):
            return False
        for i,j in combinations(nbr,2):
            common=rows[i]&rows[j]&~(1<<v)
            for k in range(len(rows)):
                if common>>k&1 and any(counts[tuple(sorted(edge))]>=3
                                       for edge in ((v,i),(i,k),(k,j),(j,v))):
                    return False
    return True


def main():
    import networkx as nx
    tally=0
    for g in nx.graph_atlas_g():
        rows=graph(len(g),g.edges())
        ok=recognize(rows)
        assert ok==direct_recognition(rows)
        ws=list(supports(rows))
        for p,q in combinations(range(len(rows)),2):
            expected=[w for w in ws if w>>p&w>>q&1]
            ans,w=solve(rows,p,q)
            assert ans=='UNKNOWN' or (ans=='YES')==bool(expected)
            assert w is None or w in expected
            assert ans!='UNKNOWN' or not ok
            tally+=1
    # The root cone of the ten-site obstruction rejects the direct degree condition.
    obstruction=[770,569,800,386,2,262,512,8,557,327]
    assert solve(obstruction,5,6,False)==('UNKNOWN',None)
    # Both open and closed twin folding rescue an otherwise unrecognized disjoint component.
    r=[22,41,1,2,97,146,400,352,704,256]
    for junk,pairs in ((6,combinations(range(6),2)),(8,[(i,j) for i in range(3) for j in range(3,8)])):
        h=graph(junk,pairs)
        raw=r+[v<<len(r) for v in h]
        assert not recognize(raw) and solve(raw,6,9,False)==('UNKNOWN',None)
        assert solve(raw,6,9)==('YES',1023)
        reduced,ids=fold(raw,6,9)
        assert len(ids)<len(raw) and recognize(reduced)
    # Keep two compulsory true twins, and keep at most one other member.
    clique=graph(7,combinations(range(7),2))
    assert len(fold(clique,0,1)[1])==3
    # Exchange one edge between Q4 and a six-arm theta graph; the result is biconnected.
    cube=[(i,i^(1<<b)) for i in range(16) for b in range(4) if not i>>b&1]
    cube.remove((0,1))
    theta=[e for j in range(6) for e in ((16,18+2*j),(18+2*j,19+2*j),(19+2*j,17))]
    theta.remove((16,18))
    r=graph(30,cube+theta+[(0,16),(1,18)])
    assert nx.is_biconnected(nx.Graph(cube+theta+[(0,16),(1,18)]))
    assert recognize(r) and max(multiplicities(r).values())>=3 and max(v.bit_count() for v in r)==6
    for p,q in ((0,17),(5,21),(16,17)):
        ans,w=solve(r,p,q,False)
        assert ans=='YES' and w>>p&w>>q&1
    # The four-neighbor child-claw saturation check is reached in an unbounded-degree host.
    pairs=[(2*i,2*i+1) for i in range(18)]
    cap=(36,37)
    raw=physical_walk(pairs,cap,'edges',[(36,0),(36,3),(36,5)])
    # Add a detached eight-leaf star: there is a high site but it is not on the chord triangle.
    base=len(raw)
    raw+= [v<<base for v in graph(9,[(0,i) for i in range(1,9)])]
    assert repair(raw,pairs,cap,'edges')
    print(tally,'atlas pin pairs; true/false twins, biconnected cube/theta, triangle saturation verified')


if __name__=='__main__':
    main()
