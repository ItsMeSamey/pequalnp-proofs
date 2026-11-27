from itertools import combinations,product
from random import Random
from bipartite_matching_hull import prepare,solve,reduce


def main():
    rng=Random(197)
    total=0
    for k in range(30):
        n=4
        es=[(a,b,tuple(rng.randrange(3) for _ in range(3)))
            for a in (0,1) for b in (2,3) for _ in range(rng.randrange(3))]
        match=[ids for ids in combinations(range(len(es)),2)
               if len({u for i in ids for u in es[i][:2]})==4]
        gain=lambda ids:tuple(sum(es[i][2][j] for i in ids)%3 for j in range(3))
        hull=prepare(n,es,3)
        if not match:
            assert hull is None
            continue
        base,o,basis,cycles=hull
        span={(0,0,0)}
        for ids in match:
            diff=tuple((x-y)%3 for x,y in zip(gain(ids),o))
            span={tuple((a+t*b)%3 for a,b in zip(v,diff)) for v in span for t in range(3)}
        assert len(span)==3**len(basis)
        assert all(not any(reduce(v,basis)) for v in span)
        assert len(cycles)==len(basis)
        for target in product(range(3),repeat=3):
            status,w,r=solve(n,es,target,rounds=14,randbelow_fn=rng.randrange)
            assert (status=="SAT")==any(gain(ids)==target for ids in match),(k,target,status,r,es,base,o,basis)
            if w is not None:
                assert tuple(sorted(w)) in match and gain(w)==target
            total+=1
    print(total,"target checks passed")


if __name__=="__main__":
    main()
