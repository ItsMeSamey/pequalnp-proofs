from random import Random
from itertools import product
from one_defect_redundant_2sat import search


def verify(rows,b,**kwargs):
    valid={z for z in range(1<<len(rows)) if (z&b).bit_count()%2 and
           all(not(z>>i&1 and (z&r).bit_count()%2) for i,r in enumerate(rows))}
    status,w,stats=search(rows,b,**kwargs)
    assert status=='UNKNOWN' or (status=='YES')==bool(valid)
    assert w is None or w in valid
    return status,w,stats


if __name__=='__main__':
    rows=[39,14,13,59,18,44]
    for j in range(6):
        s,w,m=verify(rows,63,pivot=j)
        assert (s,w)==('YES',55)
        print('pivot',j,'h',m['h'])
    assert verify(rows,63,h_cap=0)[0]=='UNKNOWN'
    for rows in product(range(8),repeat=3):
        for b in range(8):
            assert verify(rows,b)[0]!='UNKNOWN'
    rng=Random(23)
    for _ in range(500):
        n=rng.randrange(4,9)
        verify([rng.randrange(1<<n) for i in range(n)],rng.randrange(1<<n),
               h_cap=rng.randrange(5),layout_cap=rng.choice([0,27,729]))
    print('4096 exhaustive, 500 random, bounded refusal passed')
