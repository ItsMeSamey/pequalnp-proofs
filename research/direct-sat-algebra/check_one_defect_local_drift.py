from itertools import product
from random import Random
from one_defect_local_drift import completion,count,search


def rank(vs):
    s={0}
    for v in vs:
        s.update([t^v for t in s])
    return len(s).bit_length()-1


if __name__=='__main__':
    rng=Random(391)
    for _ in range(300):
        n=rng.randrange(1,6)
        M=[rng.randrange(8) for i in range(n)]
        C=[rng.randrange(8)&~m for m in M]
        opt=min(rank(P) for P in product(*[[v for v in range(8) if v&~m==c] for m,c in zip(M,C)]))
        for s in range(4):
            got=completion(C,M,s)
            assert (got is not None)==(s>=opt)
            if got is not None:
                assert rank(got)<=s and all(v&~m==c for v,m,c in zip(got,M,C))
    def test(rows,b,s):
        good={z for z in range(1<<len(rows)) if (z&b).bit_count()%2 and all(not(z>>i&1 and (z&r).bit_count()%2) for i,r in enumerate(rows))}
        ways,w=search(rows,b,s)
        assert ways is None or (ways==len(good) and (w in good if ways else w is None)),(rows,b,s,ways,good,w)
        return ways
    for rows in product(range(8),repeat=3):
        for b in range(8):
            assert test(rows,b,3) is not None
    for _ in range(180):
        n=rng.randrange(1,8)
        test([rng.randrange(1<<n) for i in range(n)],rng.randrange(1,1<<n),rng.randrange(4))
    assert test([39,14,13,59,18,44],63,3)==1
    print('300 completion optima, 4096 exhaustive counts/witnesses, 180 random cases, unique 55 control passed')
