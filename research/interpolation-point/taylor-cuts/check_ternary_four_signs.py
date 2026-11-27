from itertools import product
from random import Random
from ternary_four_signs import solve

def check(rows,rhs,n):
    oracle = next((s for s in product((1,2),repeat=n)
                   if all(sum(x*y for x,y in zip(s,row))%3==b for row,b in zip(rows,rhs))),None)
    status,witness,stats=solve(rows,rhs,n=n,high_cap=n,ambiguous_cap=len(rows))
    assert (status == 'SAT') == bool(oracle is not None) and status!='UNKNOWN', (rows,rhs,status)
    if witness is not None:
        assert all(x in (1,2) for x in witness)
        assert all(sum(x*y for x,y in zip(witness,row))%3==b for row,b in zip(rows,rhs))
    return stats

if __name__=='__main__':
    for pat in product((1,2),repeat=4):
        for b in product(range(3),repeat=2):
            check([(1,)*4,pat],b,4)
    rng=Random(718)
    for _ in range(450):
        n=rng.randrange(1,8)
        rows=[]
        for j in range(rng.randrange(9)):
            row=[0]*n
            for k in rng.sample(range(n),rng.randrange(min(n,4)+1)):
                row[k]=rng.choice((1,2))
            rows.append(row)
        check(rows,[rng.randrange(3) for row in rows],n)
    rows=[[int(i==0 or 3*j<i<=3*j+3) for i in range(10)] for j in range(3)]
    assert solve(rows)[0]=='UNKNOWN'
    assert solve(rows,high_cap=1)[0]=='SAT'
    assert solve([[1]*4,[2,1,1,1]])[0]=='UNSAT'
    print('594 differential systems plus three explicit cap/parity controls passed')
