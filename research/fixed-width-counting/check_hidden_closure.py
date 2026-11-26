"""Check hidden atom inversion and residue packing with a crossing visible core."""
from itertools import product
from math import prod
from random import Random


def profiles(h,tails):
    keys = {(0,0)}
    for m,b in tails:
        keys |= {(m|u,b|v) for u,v in keys if not (b^v)&m&u}
    weights = {}
    for m,b in sorted(keys,key=lambda k:-k[0].bit_count()):
        weights[m,b] = (1<<(h-m.bit_count()))-sum(
            w for (u,v),w in weights.items() if u&m==m and v&m==b)
    assert min(weights.values())>=0 and sum(weights.values())==1<<h
    return [(u,w) for u,w in weights.items() if w]


def run(v, blocks, core):
    entries = [profiles(h,[(m,b) for m,b,vm,vb in clauses]) for h,clauses in blocks]
    total = [0]*3
    for x in range(1<<v):
        if any(x&m==b for m,b in core):
            continue
        oracle = [1,1,1]
        for (h,clauses),local in zip(blocks,entries):
            raw = sum(all(y&m!=b or x&vm!=vb for m,b,vm,vb in clauses) for y in range(1<<h))
            viable = [w for (u,t),w in local if all(
                u&m!=m or t&m!=b or x&vm!=vb for m,b,vm,vb in clauses)]
            assert sum(viable)==raw
            oracle[0]*=raw
            for j,p in enumerate((3,5),1):
                bitmax = 1<<(p-1).bit_length()
                count = sum(i%p< w%p and i<p for w in viable for i in range(bitmax))
                oracle[j]*=count
        total = [a+b for a,b in zip(total,oracle)]
    assert all(total[j]%p==total[0]%p for j,p in enumerate((3,5),1))


if __name__=='__main__':
    rng = Random(42)
    for _ in range(400):
        v = rng.randrange(5)
        def cube(s):
            m = rng.randrange(1<<s)
            return (m,rng.randrange(1<<s)&m)
        blocks = []
        for _ in range(rng.randrange(1,4)):
            h = rng.randrange(5)
            blocks.append((h,[cube(h)+cube(v) for _ in range(rng.randrange(8))]))
        run(v,blocks,[cube(v) for _ in range(rng.randrange(3))])
    print('400 hidden-atom and multiple-block residue compression checks passed')
