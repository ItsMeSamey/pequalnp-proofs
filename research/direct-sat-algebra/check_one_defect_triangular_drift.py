from itertools import product
from random import Random
from one_defect_triangular_drift import minimum_completion,search
from quadratic_target import apply_basis,parity


def rank(cols):
    out={0}
    for v in cols:
        out.update([x^v for x in out])
    return len(out).bit_length()-1


def trial(rows,b):
    good={z for z in range(1<<len(rows)) if parity(b&z) and all(not(z>>i&1 and parity(v&z)) for i,v in enumerate(rows))}
    status,w,_=search(rows,b)
    assert (status=='YES')==bool(good) and (w in good if good else w is None)


if __name__=='__main__':
    for n in range(1,5):
        minima={}
        for rows in product(range(1<<n),repeat=n):
            key=tuple(v&((1<<i)-1) for i,v in enumerate(rows))
            minima[key]=min(minima.get(key,n),rank(rows))
        for key,opt in minima.items():
            V,U=minimum_completion(key)
            assert len(V)==opt
            assert all(apply_basis(V,u)&((1<<i)-1)==key[i] for i,u in enumerate(U))
    for rows in product(range(8),repeat=3):
        for b in range(8):
            trial(rows,b)
    rng=Random(455)
    for _ in range(250):
        n=rng.randrange(2,9)
        trial([rng.randrange(1<<n) for i in range(n)],rng.randrange(1<<n))
    rows=[39,14,13,59,18,44]
    assert search(rows,63)[:2]==('YES',55) and search(rows,63,rank_cap=0)[0]=='UNKNOWN'
    print('All completion minima through 4x4, 4096 exhaustive native decisions, 250 random cases, witness 55 and cap passed')
