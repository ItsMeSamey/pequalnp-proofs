from random import Random
from native_intersection import solve,evaluate

if __name__=='__main__':
    rng=Random(622)
    counts={}
    for _ in range(120):
        n=rng.randrange(7)
        g=[tuple(rng.getrandbits(n+j+1) for _ in (0,1)) for j in range(rng.randrange(1,9))]
        o=1<<(n+len(g));orders=[list(range(n)),list(range(n))]
        for row in orders:rng.shuffle(row)
        truth=[x for x in range(1<<n) if evaluate(n,g,o,x)]
        r=solve(n,g,o,orders)
        assert r['status']==('sat' if truth else 'unsat'),(n,g,o,r)
        if truth:assert r['witness'] in truth
        key=(r['route'],r['status']);counts[key]=counts.get(key,0)+1
        assert solve(n,g,o,orders,budget=0)['status']=='skip'
    n=6
    parity=2|4|8
    g=[(parity^1,16),(parity,1<<(n+1))]
    orders=[list(range(n)),list(reversed(range(n)))]
    assert solve(n,g,1<<(n+2),orders,fallback=False)['status']=='unsat'
    r=solve(n,g,parity,orders)
    assert r['route']=='same-order fallback' and r['status']=='sat'
    print(counts)
