from random import Random
from proxy import recode,solve_cnf,accepts_cnf,solve


def fixture(m):
    t=m+1;rows=[]
    for i in range(m):
        s=i+1;x=m+2+5*i;y=x+1;u=x+2;v=x+3;z=x+4
        rows.extend([(s,-x),(s,-y),(-s,x),(s,-x,z)])
        for lhs,rhs in ((x,u),(y,v)):
            rows.extend([(t,-lhs,rhs),(t,lhs,-rhs),(-t,-lhs,-rhs),(-t,lhs,rhs)])
    n=6*m+1
    return n+6,rows+[(n+1,n+3,n+4),(n+2,n+5,n+6),(n+1,n+2)]


if __name__=='__main__':
    rng=Random(90311)
    for _ in range(90):
        n=rng.randint(1,6)
        raw=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randint(1,3))) for i in range(rng.randint(3,11))]
        rec,orig,data,masters,copies=recode(n,raw)
        selectors={min(map(abs,r)) for r in rec if len(r)==3}
        assert selectors=={orig[v] for v in masters}
        assert all(sum(abs(l) in selectors for l in r)<=1 for r in rec)
        decoded=[]
        for y in range(1<<(n+len(copies))):
            if accepts_cnf(rec,y):
                decoded.append(sum(((y>>(orig[v]-1))&1)<<(v-1) for v in orig))
        truth=[x for x in range(1<<n) if accepts_cnf(raw,x)]
        assert sorted(decoded)==truth
        r=solve_cnf(n,raw)
        assert r['status']==('sat' if truth else 'unsat')
        if truth:assert r['witness'] in truth
    for m in (2,3):
        n,rows=fixture(m)
        for contradiction in (False,True):
            raw=rows+([(m+1,),(-m-1,)] if contradiction else [])
            assert solve(n,raw)['route']=='proposed decomposition has multiple guards'
            r=solve_cnf(n,raw)
            c=r['cost']
            assert r['status']==('unsat' if contradiction else 'sat')
            assert c['copies'] and c['essential_strict']>=m
            print(m,r['status'],c['copies'],c['essential_strict'],c['first_essential'])
