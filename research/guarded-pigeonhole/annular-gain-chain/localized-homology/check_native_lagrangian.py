"""Exhaust local fibers; test the greedy plane algorithm on affine graph codes."""
from itertools import product, combinations
from random import Random


def pairing(x,y):
    return ((x & (y>>2)) ^ ((x>>2) & y)).bit_count() % 2


def local():
    native={0,1,2,3,4,8,12}
    for e in range(1,16):
        if ((e&3)&(e>>2)).bit_count()%2:
            continue
        mixed=bool(e&3 and e>>2)
        for bit in range(2):
            reps={min(a,a^e) for a in native if pairing(a,e)==bit}
            assert len(reps)==((2,4) if mixed else (3,2))[bit]


def test(case,rng):
    n=case%6+1
    adj=[0]*n
    for i in range(n):
        for j in range(i,n):
            if rng.randrange(2):
                adj[i]|=1<<j
                adj[j]|=1<<i
    shift=[rng.randrange(4) for _ in range(n)]
    words=[tuple(shift[i]^(((x>>i)&1) | (2*((x&adj[i]).bit_count()%2)))
                 for i in range(n)) for x in range(1<<n)]
    states=[set(rng.sample(range(4),rng.randrange(2,5))) for _ in range(n)]
    truth=any(all(x in s for x,s in zip(word,states)) for word in words)
    remaining=[w for w in words if all(len(s)!=2 or x in s for x,s in zip(w,states))]
    if not remaining:
        assert not truth
        return
    for i,s in enumerate(states):
        if len(s)==2:
            continue
        image={w[i] for w in remaining}
        assert len(image)>=2
        p=min(image&s)
        line=next(set(t) for t in combinations(sorted(s),2) if p in t)
        remaining=[w for w in remaining if w[i] in line]
    assert truth and remaining and all(w[i] in states[i] for w in remaining for i in range(n))


if __name__=='__main__':
    local()
    rng=Random(7183)
    for case in range(10000):
        test(case,rng)
    print('All 18 nonzero-singular-generator local fibers and 10000 affine plane products verified.')
