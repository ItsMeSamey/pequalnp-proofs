from random import Random
from proposer import solve
from native_intersection import evaluate

if __name__=='__main__':
    rng=Random(4930)
    paths={}
    for _ in range(100):
        n=rng.randrange(7)
        gates=[tuple(rng.getrandbits(n+j+1) for _ in (0,1)) for j in range(rng.randrange(1,8))]
        out=1<<(n+len(gates))
        r=solve(n,gates,out,budget=75000,rank_cap=16)
        truth=[i for i in range(1<<n) if evaluate(n,gates,out,i)]
        paths[r['status']]=paths.get(r['status'],0)+1
        assert sum(a['cap'] for a in r['cost']['attempts'])<=75000
        if r['status']=='sat': assert r['witness'] in truth
        if r['status']=='unsat':assert not truth
        assert solve(n,gates,out,budget=0)['status']=='skip'
    print(paths)
