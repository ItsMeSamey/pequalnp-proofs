from itertools import combinations,product
from random import Random
from dense_pair_hashes import colorings,small_family
from dense_colored_matching import solve


def all_matchings(edges,live):
    if not live:
        yield ()
        return
    u=min(live)
    for i,(a,b,_) in enumerate(edges):
        if u in (a,b) and a in live and b in live:
            for rest in all_matchings(edges,live-{a,b}):
                yield (i,)+rest


def main():
    for n,k in ((3,0),(5,1),(17,2),(11,3),(12,4),(6,4)):
        missing=set(combinations(range(n),k))
        for colors in colorings(n,k):
            missing={s for s in missing if len({colors[i] for i in s})!=k}
            if not missing:break
        assert not missing
    for t in (2,3):
        assert all(any(len({f[i] for i in s})==t for f in small_family(10,t))
                   for s in combinations(range(10),t))
    rng=Random(3901)
    checks=0
    for _ in range(20):
        pairs=[(0,3),(1,4),(2,5)]
        pairs += [(i,j) for i in range(3) for j in range(3,6) if rng.randrange(3)]
        edges=[(v,w,(rng.randrange(3),rng.randrange(3))) for v,w in pairs]
        pm=[tuple(sorted(M)) for M in all_matchings(edges,set(range(6)))]
        def gain(M):
            return tuple(sum(edges[i][2][j] for i in M)%3 for j in range(2))
        image={gain(M) for M in pm}
        for t in product(range(3),repeat=2):
            st,w,_=solve(6,edges,(0,1,2),t,left=range(3),deleted=(0,))
            assert (st=="SAT")==(t in image) and st!="UNKNOWN"
            if w is not None:assert tuple(sorted(w)) in pm and gain(w)==t
            checks+=1
    print("8 hash coverage tests;",checks,"exact matching decisions")
if __name__=="__main__":
    main()
