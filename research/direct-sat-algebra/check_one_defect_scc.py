from itertools import product
from random import Random
from one_defect_scc import search, symmetric_generators
from quadratic_target import parity, insert


def feasible(rows,x):
    return all(not(x>>i&1 and parity(r&x)) for i,r in enumerate(rows))


def verify(rows,beta,cap):
    status,x,_=search(rows,beta,local_cap=cap)
    yes=any(feasible(rows,z) and parity(z&beta) for z in range(1<<len(rows)))
    assert status=='UNKNOWN' or ((status=='YES')==yes)
    if x is not None:
        assert feasible(rows,x) and parity(x&beta)
    return status


if __name__=='__main__':
    for rows in product(range(8),repeat=3):
        for beta in range(8):
            verify(rows,beta,3)
    rng=Random(351)
    stats={}
    for _ in range(850):
        n=rng.randrange(1,10)
        rows=[rng.randrange(1<<n) for i in range(n)]
        s=verify(rows,rng.randrange(1<<n),rng.randrange(6))
        stats[s]=stats.get(s,0)+1
    for _ in range(250):
        n=rng.randrange(1,9)
        rows=[0]*n
        for j in range(n):
            for i in range(j+1):
                if rng.randrange(2):
                    rows[i]|=1<<j
                    rows[j]|=1<<i
        basis={}
        for z in symmetric_generators(rows):
            assert feasible(rows,z)
            insert(z,0,basis)
        size=len(basis)
        for z in range(1<<n):
            if feasible(rows,z):
                insert(z,0,basis)
        assert size==len(basis)
    # Two independent incoming coordinates enter one cyclic symmetric block.
    status,_,trace=search([0,0,9,6],12,local_cap=0)
    assert status=='UNKNOWN' and trace[-1][1]==2
    print('4096 exhaustive decisions, 850 random decisions',stats,'250 symmetric span checks, rank-2 refusal passed')
