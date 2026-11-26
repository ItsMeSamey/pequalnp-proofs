#!/usr/bin/env python3
"""Greedy Strahler recognition versus unrestricted root optimization on tiny cubes."""
from functools import lru_cache
from itertools import combinations
from random import Random
from check_robust import solve


def check(n,leaf,order,expect_hereditary=True):
    size=1 << n
    full=(1 << size)-1
    bits=[sum(1 << x for x in range(size) if x >> i & 1) for i in range(n)]
    def parts(cell):
        for j in order:
            high=cell & bits[j]
            low=cell ^ high
            if high and low:
                yield high,low
    @lru_cache(None)
    def rank(cell):
        if leaf(cell):
            return 0
        best=n+2
        for a,b in parts(cell):
            x,y=rank(a),rank(b)
            best=min(best,max(x,y)+(x==y))
        return best
    @lru_cache(None)
    def greedy(cell,r):
        if leaf(cell):
            return sum(x*x+1 for x in range(size) if cell >> x & 1)
        if r == 0:
            return None
        for a,b in parts(cell):
            for side,other in [(a,b),(b,a)]:
                small=greedy(side,r-1)
                if small is not None:
                    rest=greedy(other,r)
                    return None if rest is None else small+rest
        return None
    expected=sum(x*x+1 for x in range(size))
    for r in range(n+1):
        result=greedy(full,r)
        if result is not None:
            assert result==expected
        if expect_hereditary:
            assert (result is not None) == (rank(full)<=r)
    return rank(full),greedy(full,1)


def main():
    rng=Random(1617)
    count=0
    for n in (2,3,4):
        size=1<<n
        for _ in range(50):
            # Arbitrary forbidden-subset antichain presentation (redundancy allowed).
            forbidden=[sum(1<<x for x in rng.sample(range(size),rng.randint(2,min(size,5))))
                       for _ in range(rng.randrange(12))]
            order=rng.sample(range(n),n)
            check(n,lambda cell: not any(cell&f==f for f in forbidden),order)
            p=rng.randrange(1,5)
            masks=[rng.randrange(1,1<<p) for _ in range(size)]
            d=rng.randrange(1,min(3,p)+1)
            features=[i for i in range(1,1<<p) if i.bit_count()<=d]
            rows=[[int(mask & i == i) for i in features] for mask in masks]
            @lru_cache(None)
            def fits(cell):
                return solve([row for i,row in enumerate(rows) if cell>>i & 1],len(features)) is not None
            check(n,fits,order)
            count+=2
    n=3
    hyper=lambda j,b: sum(1<<x for x in range(8) if (x>>j & 1)==b)
    # Both x0 hyperplanes are leaves, and one x1 hyperplane is also a leaf.
    allowed={hyper(0,0),hyper(0,1),hyper(1,1)}
    rank,answer=check(3,lambda cell: cell.bit_count()==1 or cell in allowed,[1,0,2],False)
    assert rank==1 and answer is None
    print(f"{count} hereditary cases matched all optimal rank thresholds and additive counts; nonhereditary counterexample confirmed.")


if __name__=='__main__':
    main()
