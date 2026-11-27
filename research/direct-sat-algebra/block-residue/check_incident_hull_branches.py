"""04-only comparison with every original orientation, bypassing gadget logic."""
from itertools import product
from incident_port import forest_chords, incident_directions


def span(vectors):
    values={0}
    for v in vectors:
        values|={a^v for a in values}
    return values


def check(n,edges,chords,pairs):
    assert tuple(forest_chords(n,edges))==chords
    words={}
    for mask in range(1<<len(edges)):
        odd=0
        for i,(x,y) in enumerate(edges):
            if mask>>i&1:odd^=(1<<x)^(1<<y)
        if not odd:
            coordinate=sum(((mask>>e)&1)<<j for j,e in enumerate(chords))
            assert coordinate not in words
            words[coordinate]=mask
    assert len(words)==1<<len(chords)
    cols=[sum(((words[1<<j]>>e)&1)<<j for j in range(len(chords))) for e in range(len(edges))]
    exact=set.intersection(*(span(cols[p[b]] for p,b in zip(pairs,bits))
                             for bits in product((0,1),repeat=len(pairs))))
    got=incident_directions(n,edges,pairs,method='hull')
    assert span(got)==exact and len(exact)==1<<len(got)
    return exact


def main():
    square=[(0,1),(1,2),(2,3),(3,0),(0,2)]
    # Dropping edge 0 makes old chord 3 a greedy-forest edge. It still lies
    # on the triangle (2,3,4), so its original coordinate cannot be dropped.
    ids=[1,2,3,4]
    residual=[square[i] for i in ids]
    assert tuple(ids[j] for j in forest_chords(4,residual))==(4,)
    assert check(4,square,(3,4),[(0,2)])=={0}
    assert check(4,square,(3,4),[(0,2),(1,4)])=={0,3}
    # Two square+diagonal blocks share only vertex 3. Pairs 0--2 and 5--7
    # are disjoint-ended inside their blocks; 1--8 crosses the separator.
    edges=square+[(3,4),(4,5),(5,6),(6,3),(3,5)]
    check(7,edges,(3,4,8,9),[(0,2),(5,7),(1,8),(4,9)])
    # A nonincident cross-block pair with a singleton loop.
    check(5,square+[(4,4)],(3,4,5),[(0,2),(4,5)])
    print('four exact original-orientation hull targets, including reforested chord 3')


if __name__=='__main__':main()
