from random import Random
from itertools import product
from check_one_defect_uniform_tournament import tournament,supports
from one_defect_mixed_skeleton import search


def test(rows,b,diag,k):
    G=[r^((diag>>i&1)<<i) for i,r in enumerate(rows)]
    good=[z for z in supports(G) if (z&b).bit_count()%2]
    status,w=search(rows,b,deletions=k,offset=diag)
    assert status=='UNKNOWN' or (status=='YES')==bool(good)
    assert w is None or w in good
    ways,rep=search(rows,b,deletions=k,offset=diag,exact_count=True)
    assert ways is None or ways==len(good)
    assert rep is None or rep in good
    return status


if __name__=='__main__':
    counts={}
    for n in range(1,5):
        for code in range(1<<(n*(n-1)//2)):
            rows=tournament(n,code)
            for b,diag in product(range(1<<n),repeat=2):
                s=test(rows,b,diag,1)
                counts[s]=counts.get(s,0)+1
    rng=Random(590)
    for _ in range(550):
        n=rng.randrange(5,11)
        test(tournament(n,rng.getrandbits(n*(n-1)//2)),rng.randrange(1<<n),rng.randrange(1<<n),rng.randrange(4))
    print('All tournaments, marks, offsets through n=4',counts,'plus 550 random cases passed')
