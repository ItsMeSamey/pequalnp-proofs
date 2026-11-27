from itertools import product
from random import Random
from fd_clock import solve_cnf,accepts_cnf

def family(m,kind):
    w=m+1; rows=[]
    for i in range(m):
        s=i+1;x=m+2+i;z=2*m+2+i;u=3*m+2+i;v=4*m+2+i
        if kind=='free':
            rows.append((s,x,u))
        else:
            rows.extend([(s,-x),(-s,x),(s,u,v)])
        if kind=='rigid':rows.append((w,x,z))
        else:
            for a,b,c in product((0,1),repeat=3):
                if a^b^c:rows.append(tuple(-j if t else j for j,t in zip((w,x,z),(a,b,c))))
    return 5*m+1,rows

if __name__=='__main__':
    for mode in ('symmetric','rigid','free'):
        n,rows=family(5,mode)
        result=solve_cnf(n,(iter(r) for r in rows),key_bound_cap=None)
        assert result['status']=='sat' and accepts_cnf(rows,result['witness'])
        cut=result['cost']['cuts'][-2]
        print(mode,cut,result['cost']['retained'][-2])
        assert (cut['c'],cut['d'])=={'symmetric':(0,0),'rigid':(0,5),'free':(5,0)}[mode]
        bounded=solve_cnf(n,(iter(r) for r in rows),key_bound_cap=1)
        if mode=='symmetric':
            assert bounded['status']=='sat'
        else:
            assert bounded['status']=='skip' and bounded['cost']['generated']==bounded['cost']['binary_probes']==0
    rng=Random(712)
    for _ in range(80):
        n=rng.randrange(1,7)
        rows=[tuple(rng.choice((-1,1))*rng.randint(1,n) for j in range(rng.randrange(4))) for i in range(rng.randrange(1,12))]
        r=solve_cnf(n,(iter(c) for c in rows),key_bound_cap=None)
        truth=[x for x in range(1<<n) if accepts_cnf(rows,x)]
        assert r['status']==('sat' if truth else 'unsat')
        assert not truth or r['witness'] in truth
        assert r['cost']['generated']<=r['cost']['candidate_bound']
