from hidden import fixture
from solver import solve,accepts_cnf
import json
rows=[]
for b in range(1,8):
    for bad in [False,True]:
        n,cs,_,_=fixture(3,b,bad,815)
        r=solve(n,cs,b=b,extract_arities=(3,),orient=True,exponent_cap=0,detect_blocks=True)
        c=r['cost']
        assert r['status']==('unsat' if bad else 'sat')
        assert c['cover_method']=='scope_intersections' and c['search_nodes']==0 and len(c['cover'])==b
        assert all(a['method']=='2sat' for a in c['cosets'])
        if bad:assert len(c['cosets'])==1<<b
        else:assert accepts_cnf(cs,r['witness'])
        rows.append(dict(b=b,n=n,clauses=len(cs),status=r['status'],cosets=len(c['cosets']),ns=c['elapsed_ns']))
print(rows[-2:])
open('growth.json','w').write(json.dumps(rows,indent=2)+'\n')
