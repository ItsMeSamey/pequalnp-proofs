from random import Random
from successor import solve,solve_cnf,accepts_cnf
if __name__=='__main__':
    rng=Random(1227);counts={}
    for _ in range(100):
        n=rng.randrange(1,7)
        cs=[tuple(rng.choice((-1,1))*rng.randint(1,n) for j in range(rng.randrange(1,5))) for i in range(rng.randrange(2,10))]
        models=[x for x in range(1<<n) if accepts_cnf(cs,x)]
        for opts in ({},{'peel_steps':0}):
            r=solve_cnf(n,cs,**opts)
            counts[r['route']]=counts.get(r['route'],0)+1
            if r['status']=='sat':assert r['witness'] in models
            if r['status']=='unsat':assert not models
    n=6;g=[];ends=[]
    for off in (0,1):
        v=2<<off
        for j in range(1,5):
            x=2<<(j+off);g.append((v,x));z=1<<(n+len(g));v=z if j%2 else z^v^x
        ends.append(v)
    g.append(tuple(ends));out=1<<(n+len(g))
    orders=((0,1,2,4,3,5),(1,2,3,5,4,0))
    for opts,route in [({},'affine-cell intersection'),({'peel_steps':0},'any order')]:
        r=solve(n,g,out,orders=orders,**opts)
        assert r['status']=='sat' and r['route']==route,r
        print(route,r['cost'].get('cell_sizes'),len(r['cost']['factor_calls']))
    assert solve(n,g,out,orders=orders,peel_steps=0,linear_work=0)['status']=='skip'
    for cs,want in [([(-1,),(-2,),(1,2)],'unsat'), ([(1,2),(-1,2)],'sat')]:
        assert solve_cnf(2,cs)['status']==want
    print(counts)
