"""Independent enumeration of optimal gauge support and oracle answers."""
from itertools import combinations, product
from functools import reduce
from operator import xor
from random import Random


def rank(columns):
    pivots = {}
    for v in columns:
        while v:
            i = v.bit_length() - 1
            if i not in pivots:
                pivots[i] = v
                break
            v ^= pivots[i]
    return len(pivots)


def total(columns):
    return reduce(xor, columns, 0)


def subsets(indices):
    for k in range(len(indices)+1):
        yield from combinations(indices,k)


def run():
    units = [1,2,4,8]
    a = units+[14,13,11,7]
    ranks = [rank([v for i,v in enumerate(a) if s>>i&1]) for s in range(256)]
    minimum = 4
    for d in product(range(16),repeat=4):
        residual = sum(1<<i for i,v in enumerate(a)
                       if total(d[k] for k in range(4) if v>>k&1) != (v if i<4 else 0))
        minimum = min(minimum,ranks[residual])
    assert minimum==4
    rng=Random(313)
    for _ in range(200):
        a=[rng.randrange(32) for _ in range(rng.randrange(1,9))]
        flat=rng.choices(a,k=rng.randrange(5))
        gains=[rng.randrange(16) if rank([*flat,v])==rank(flat) else 0 for v in a]
        support={i for i,v in enumerate(gains) if v}
        d=[rng.randrange(16) for _ in range(5)]
        dense=[g ^ total(d[k] for k in range(5) if v>>k&1) for v,g in zip(a,gains)]
        circuits=[]
        for indices in subsets(range(len(a))):
            cols=[a[i] for i in indices]
            if cols and not total(cols) and rank(cols)==len(cols)-1:
                circuits.append(set(indices))
        direct={total(dense[i] for i in c) for c in circuits}
        answers={total(gains[i] for i in c) for c in circuits if c<=support and len(c)<=5}
        for indices in subsets(support):
            s=set(indices)
            if len(s)<=4 and rank([a[i] for i in s])==len(s):
                if any(c & support == s for c in circuits):
                    answers.add(total(gains[i] for i in s))
        assert direct==answers
    print('65536 gauges, minimum support rank 4; 3200 target comparisons')


if __name__=='__main__':
    run()
