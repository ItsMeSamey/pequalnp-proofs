from itertools import combinations,product
from random import Random
from one_defect_clause_closure import search,samples,solve_clauses
from quadratic_target import parity,insert


def evaluation(y,n):
    masks=[0]+[1<<i for i in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
    return sum((y&s==s)<<i for i,s in enumerate(masks))


def test(rows,b,p=None,solver=search):
    status,w,_=solver(rows,b,p)
    valid={z for z in range(1<<len(rows)) if parity(z&b) and
           all(not(z>>i&1 and parity(z&r)) for i,r in enumerate(rows))}
    assert status=='UNKNOWN' or (status=='YES')==bool(valid)
    assert (w in valid) if status=='YES' else w is None
    return status,bool(valid)


if __name__=='__main__':
    rng=Random(71)
    for n in range(7):
        for _ in range(35):
            H=[(rng.randrange(2*n),rng.randrange(2*n)) for i in range(rng.randrange(3*n+1))]
            full=[y for y in range(1<<n) if all(not(y>>(a//2)&1==a%2 and y>>(b//2)&1==b%2) for a,b in H)]
            pts=samples(n,H)
            assert set(pts)<=set(full) and bool(pts)==bool(full)
            basis={}
            for y in pts:
                insert(evaluation(y,n),0,basis)
            size=len(basis)
            for y in full:
                insert(evaluation(y,n),0,basis)
            assert len(basis)==size
    counts={}
    for rows in product(range(8),repeat=3):
        for b in range(8):
            key=test(rows,b)
            counts[key]=counts.get(key,0)+1
    for _ in range(350):
        n=rng.randrange(4,8)
        rows=[rng.randrange(1<<n) for i in range(n)]
        b=rng.randrange(1,1<<n)
        key=test(rows,b,rng.choice([i for i in range(n) if b>>i&1]))
        counts[key]=counts.get(key,0)+1
    control=([69,111,228,8,154,180,107,213],180)
    assert test(*control)==('UNKNOWN',True)
    from one_defect_affine_closure import search as affine
    for rows in product(range(8),repeat=3):
        for b in range(8):
            test(rows,b,solver=affine)
    for _ in range(350):
        n=rng.randrange(4,8)
        test([rng.randrange(1<<n) for i in range(n)],rng.randrange(1<<n),solver=affine)
    print('Affine restart also passed 4446 reference decisions; fixed-coordinate feasible UNKNOWN verified')
    print('245 relaxation span tests; 4446 exact reference decisions',counts)
