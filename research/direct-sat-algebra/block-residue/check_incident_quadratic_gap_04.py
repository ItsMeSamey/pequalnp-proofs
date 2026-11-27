"""Scheduled 04 regression. Enumerate geometric potentials, never raw copy words."""
from itertools import product
from biclique_dual import dual_directions
from incident_port import forest_chords, incident_directions
from incident_total import incident_block_witness
from check_mux_single_block_04 import physical_chart
from check_branch_nand_04 import physical_source, replay


def span(rows):
    result={0}
    for v in rows:
        result |= {x^v for x in result}
    return result


def check(k):
    n=1+3*k
    edges=[]
    for i in range(k):
        a,b,c,d=0,3*i+1,3*i+2,3*i+3
        edges.extend(((a,b),(b,c),(b,d),(c,d),(c,a),(c,d)))
    pairs=list(zip(range(0,len(edges),2),range(1,len(edges),2)))
    assert forest_chords(n,edges)==tuple(6*i+j for i in range(k) for j in (3,4,5))
    # In input-order forest coordinates, CD1, CA, CD2 are the chord columns.
    cols=[v<<(3*i) for i in range(k) for v in (2,7,5,1,2,4)]
    shore=[([cols[a]],[cols[b]]) for a,b in pairs]
    assert not dual_directions(shore)
    exact=set.intersection(*(span(cols[p[b]] for p,b in zip(pairs,side))
                             for side in product((0,1),repeat=len(pairs))))
    directions=incident_directions(n,edges,pairs,method='hull')
    assert span(directions)==exact==span(2<<(3*i) for i in range(k))
    assert len(directions)==k
    for target in (0,2,(1<<(3*k))-1):
        signed=[(u,v,((target>>(3*(j//6)+j%6-3))&1) if j%6>=3 else 0)
                for j,(u,v) in enumerate(edges)]
        rows=[(signed[a],signed[b]) for a,b in pairs]
        ports,pins=physical_chart(rows)
        source=physical_source(len(rows),pins,suffix=3)
        winners=0
        for word in product((0,1),repeat=n):
            truth=all(any((word[u]^word[v])==d for u,v,d in row) for row in rows)
            raw=tuple(word[v]^offset for v,offset in ports)
            assert bool(replay(source,(*raw,0,1,0,raw[0])))==truth
            winners+=truth
        result=incident_block_witness(len(rows),pins,method='hull')
        assert winners and result is not None
        assert all((result[a]^result[b])==d for a,b,d in pins)
        for guard,y0,y1,y2 in product((0,1),repeat=4):
            assert bool(replay(source,(*result,guard,y0,y1,y2)))==(
                y0!=y1 and y1==guard and y2==result[0])


if __name__=='__main__':
    check(1)
    check(2)
    print('k=1,2: exact hull vs quadratic gap; signed quotient words and NAND witnesses replayed')
