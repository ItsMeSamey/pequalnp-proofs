from check import coupled
from coupled_order import solve as identified
from solver import solve,accepts_cnf
from random import Random
import json
rows=[]
for seed in range(48):
    rng=Random(31655+seed)
    m=2+seed%8
    n,cs=coupled(m,seed%2)
    for _ in range(2*m):
        i,j=rng.sample(range(1,2+2*m),2)
        cs.append((i*rng.choice((-1,1)),j*rng.choice((-1,1))))
    perm=list(range(1,n+1));rng.shuffle(perm);rng.shuffle(cs)
    renamed=[tuple((1 if l>0 else -1)*perm[abs(l)-1] for l in rng.sample(list(c),len(c))) for c in cs]
    r=solve(n,renamed,b=1,extract_arities=(3,),orient=True)
    r2=identified(n,renamed)
    assert r2['cost']['inferred_order'] is not None
    assert r['status']==r2['status'] and r['status'] in ('sat','unsat')
    for result in (r,r2):
        assert all(rec['method']=='2sat' for rec in result['cost']['cosets'])
        if result['status']=='sat':assert accepts_cnf(renamed,result['witness'])
    if m<=5:
        expected=False
        for x in range(1<<(2*m+1)):
            y=x
            for i in range(m):
                d=((x>>(1+2*i))^(x>>(2+2*i)))&1
                y|=(d|((d^(x&1))<<1))<<(1+2*m+2*i)
            if accepts_cnf(cs,y):expected=True;break
        assert expected==(r['status']=='sat')
    rows.append(dict(seed=seed,n=n,clauses=len(cs),status=r['status'],nodes=r['cost']['search_nodes'],cosets=len(r['cost']['cosets']),time_ns=r['cost']['elapsed_ns']))
print('48 shuffled source cases and two role-free methods;',sum(r['status']=='sat' for r in rows),'SAT')
open('permuted.json','w').write(json.dumps(rows,indent=2)+'\n')
