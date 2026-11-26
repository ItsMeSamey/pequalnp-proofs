"""Independent check in the ordinary polynomial ring, retaining powers."""
from itertools import combinations_with_replacement
from random import Random
from check import attainable, pc


def raw_pc(rows, labels, target, d):
    n=len(rows)
    mons=[t for k in range(d+1) for t in combinations_with_replacement(range(n),k)]
    ids={t:i for i,t in enumerate(mons)}
    low=sum(len(t)<d for t in mons)
    def encode(terms):
        out=0
        for t in terms:
            out ^= 1 << ids[tuple(sorted(t))]
        return out
    eq=[encode([(i,i),(i,)]) for i in range(n)]
    eq += [encode((i,j) for j in range(n) if r>>j&1) for i,r in enumerate(rows)]
    for k in range(3):
        eq.append(encode((i,) for i,c in enumerate(labels) if c>>k&1)^((target>>k)&1))
    last=-1
    while True:
        piv={}
        for p in eq:
            while p and p.bit_length() in piv:
                p ^= piv[p.bit_length()]
            if p: piv[p.bit_length()]=p
        if 1 in piv:return True
        if len(piv)==last:return False
        last=len(piv)
        eq=list(piv.values())
        for k,p in piv.items():
            if k<=low:
                for i in range(n):
                    eq.append(encode(mons[j]+(i,) for j in range(k) if p>>j&1))


def graph(a,m):
    k=len(a)
    return [v<<k for v in a]+[sum(((v>>j)&1)<<i for i,v in enumerate(a)) for j in range(m)]


if __name__=="__main__":
    rows=graph([13,3,6,10],4)
    labels=[1,5,0,5,2,6,2,0]
    assert 3 not in attainable(rows,labels)
    for d in (2,3,4):
        expected=d>=3
        assert pc(rows,labels,3,d)==raw_pc(rows,labels,3,d)==expected
    rng=Random(852)
    for _ in range(60):
        k,m=rng.randint(1,3),rng.randint(1,3)
        rows=graph([rng.randrange(1<<m) for i in range(k)],m)
        labels=[rng.randrange(8) for r in rows]
        target=rng.randrange(8)
        for d in (2,3):
            assert raw_pc(rows,labels,target,d)==pc(rows,labels,target,d)
    print("degree-3 example and 120 ordinary-ring comparisons passed")
