from itertools import combinations, product
from random import Random
from colorful_port_matching import search_coloring


def main():
    rng=Random(497)
    checks=0
    for _ in range(18):
        n=8
        edges=[(i,i+1,(0,0)) for i in range(0,n,2)]
        edges.extend((a,b,(rng.randrange(3),rng.randrange(3))) for a,b in combinations(range(n),2)
                     if rng.random()<0.38)
        base=(0,1,2,3)
        for colors in [(0,1,2,3),tuple(rng.randrange(2) for i in base)]:
            good={}
            for ids in combinations(range(len(edges)),4):
                moved=[colors[i] for i in base if i not in ids]
                if len(set(moved))!=len(moved) or len({v for i in ids for v in edges[i][:2]})!=8:
                    continue
                g=tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(2))
                good.setdefault(g,set()).add(ids)
            for t in product(range(3),repeat=2):
                w=search_coloring(n,edges,base,t,colors)
                assert (w in good[t]) if t in good else w is None
                checks+=1
    assert search_coloring(2,[(0,1,(0,)),(1,0,(2,))],(0,),(2,),(17,))==(1,)
    print(checks,"exact colorful target comparisons; parallel singleton passed")


if __name__=="__main__":
    main()
