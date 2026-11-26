from itertools import product
from random import Random
from completion import complete,combine,reduce_row

def rank(rows):
    pivots = {}
    for row in rows:
        v,_ = reduce_row(row,pivots)
        if v:
            pivots[v.bit_length()-1] = v,0
    return len(pivots)

def test(n, rows):
    vs,us = complete(n,rows)
    opts = []
    for (i,row),u in zip(rows,us):
        prefix = (1<<(i+1))-1
        assert not ((row ^ combine(vs,u)) & ~prefix)
        opts.append([(row&~prefix)|lo for lo in range(prefix+1)])
    assert len(vs) == min(rank(a) for a in product(*opts))

if __name__ == '__main__':
    rng = Random(33)
    for _ in range(300):
        n = rng.randrange(1,5)
        rows = [(rng.randrange(n),rng.randrange(1<<n)) for _ in range(rng.randrange(4))]
        test(n,rows)
    print('300 nested partial matrices compared with all completions')
    for _ in range(300):
        n = rng.randrange(1,9)
        guards = [[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))] for i in range(n)]
        indexed = [(i,mask) for i,g in enumerate(guards) for mask,c in g]
        basis,coeffs = complete(n,indexed)
        for x in range(1<<n):
            response = sum(((mask&x).bit_count()%2)<<k for k,mask in enumerate(basis))
            j = 0
            for i,g in enumerate(guards):
                if not x>>i&1:
                    j += len(g)
                    continue
                actual = []
                rebuilt = []
                for mask,c in g:
                    actual.append((mask&x).bit_count()%2 ^ c)
                    corrected = mask ^ combine(basis,coeffs[j])
                    assert corrected>>(i+1)==0
                    rebuilt.append((corrected&x).bit_count()%2 ^ c ^ ((coeffs[j]&response).bit_count()%2))
                    j += 1
                assert actual == rebuilt
    print('300 cyclic systems checked on every assignment and active guard')
