from random import Random
from itertools import product
from one_defect_native_forest import count
from quadratic_target import parity


def verify(rows,b,**kw):
    good={z for z in range(1<<len(rows)) if parity(z&b) and
          all(not(z>>i&1 and parity(z&r)) for i,r in enumerate(rows))}
    ways,w,stats=count(rows,b,**kw)
    assert len(good)==ways and (w in good if ways else w is None)
    return stats


if __name__=='__main__':
    for rows in product(range(8),repeat=3):
        for b in range(8):
            verify(rows,b)
    for i in range(6):
        rows=[39,14,13,59,18,44]
        assert count(rows,63,i)[:2]==(1,55)
    rng=Random(310)
    maxcycle=0
    for _ in range(450):
        n=rng.randrange(1,9)
        b=rng.randrange(1,1<<n)
        stats=verify([rng.randrange(1<<n) for i in range(n)],b,
                     pivot=rng.choice([i for i in range(n) if b>>i&1]),layout_cap=rng.choice([0,81,729]))
        maxcycle=max(maxcycle,max(stats.get('cycles',[]),default=0))
    assert maxcycle==2
    print('4096 exhaustive original counts, 450 random counts/witnesses, all 6 adversarial pivots, cycle rank 2 passed')
