from itertools import product
from random import Random
from point_solver import solve_cnf,oracle,accepts_cnf,parity

if __name__=='__main__':
    rng=Random(2417)
    for _ in range(60):
        n=5;binary=[tuple(rng.choice((-1,1))*rng.randint(1,n) for j in range(2)) for i in range(8)]
        # Match normalized native bank grammar.
        binary=[tuple(set(r)) for r in binary if not any(-l in r for l in r)]
        H=tuple(rng.randrange(1<<n) for j in range(rng.randrange(4)))
        goal=rng.randrange(1<<len(H));old=(1,3);word=rng.randrange(1<<n)
        costs={'oracle_calls':0,'seed_subsets':0}
        x=oracle(n,binary,old,word,H,goal,costs,(500,5000))
        truth=[y for y in range(1<<n) if accepts_cnf(binary,y) and (y^word)&5==0 and
               all(parity(h&y)==((goal>>j)&1) for j,h in enumerate(H))]
        assert (x is None and not truth) or x in truth
    for _ in range(45):
        n=rng.randint(2,6)
        raw=[tuple(rng.choice((-1,1))*rng.randint(1,n) for j in range(rng.randint(1,3))) for i in range(rng.randint(2,10))]
        truth=[x for x in range(1<<n) if accepts_cnf(raw,x)]
        r=solve_cnf(n,(iter(c) for c in raw),codim_cap=n+2)
        assert r['status']==('sat' if truth else 'unsat')
        if truth:assert r['witness'] in truth
    raw=[(1,2,3),(-1,-2,-3)]
    assert solve_cnf(3,raw,oracle_call_cap=0)['status']=='skip'
    print('60 binary+parity oracle comparisons, 45 original CNF comparisons and zero-call cap passed')
