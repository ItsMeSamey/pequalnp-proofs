from solver import solve,accepts_cnf
from itertools import product
from random import Random
import json

def xor3(a,b,c):
    return [tuple(-i if v else i for i,v in zip((a,b,c),vals)) for vals in product((0,1),repeat=3) if sum(vals)%2]

def coupled(m,unsat):
    n=1+4*m;cs=[]
    for j in range(m):
        a,b=2+2*j,3+2*j
        d,c=2+2*m+2*j,3+2*m+2*j
        cs+=xor3(a,b,d)+xor3(1,d,c)+[(a,b,-c if unsat and j==1 else c)]
        cs.append((-b,2+2*((j+1)%m)))
    if unsat:cs += [(-v,) for v in (2,3,4,5)]
    return n,cs

if __name__=='__main__':
    out=[]
    for m in (2,6,16,40):
        for unsat in (False,True):
            n,cs=coupled(m,unsat)
            r=solve(n,cs,extract_arities=(3,))
            assert r['status']==('unsat' if unsat else 'sat')
            assert r['cost']['cover']==[1] and all(c['method']=='2sat' for c in r['cost']['cosets'])
            assert solve(n,cs,b=0,extract_arities=(3,))['status']=='skip'
            if m==2:assert any(accepts_cnf(cs,x) for x in range(1<<n))!=unsat
            out.append(r)
    rng=Random(7782);routes={}
    for _ in range(750):
        n=rng.randrange(1,8)
        cs=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.choice([1,2,3,3,3]))) for j in range(rng.randrange(1,20))]
        truth=[x for x in range(1<<n) if accepts_cnf(cs,x)]
        for cap,comp in [(0,False),(8,True)]:
            r=solve(n,cs,b=rng.randrange(3),exponent_cap=cap,complete=comp,extract_arities=rng.choice([(3,),(1,2,3),()]))
            if r['status']=='skip':assert not comp
            else:
                assert (r['status']=='sat')==bool(truth)
                if truth:assert r['witness'] in truth
            for c in r['cost']['cosets']:routes[c.get('method',c['status'])]=routes.get(c.get('method',c['status']),0)+1
    open('coupled.json','w').write(json.dumps(out,indent=2)+'\n')
    print('coupled cases 8, random original-CNF outcomes 1500',routes)
    cs=xor3(1,2,5)+xor3(3,4,6)+[(5,6)]
    general=solve(6,cs,b=0,extract_arities=(3,))
    assert general['status']=='sat' and general['cost']['cosets'][0]['method']=='quadratic_gauss'
    skipped=solve(6,cs,b=0,extract_arities=(3,),exponent_cap=0)
    assert skipped['status']=='skip'
    full=solve(6,cs,b=0,extract_arities=(3,),exponent_cap=0,complete=True)
    assert full['route']=='raw_fallback' and accepts_cnf(cs,full['witness'])
    # Non-affine group with a proper affine hull: x=0, and avoid (y,z)=(1,1).
    patterns=[v for v in product((0,1),repeat=3) if v[0] or (v[1] and v[2])]
    partial=[tuple(-i if bit else i for i,bit in enumerate(v,1)) for v in patterns]
    partial_result=solve(3,partial)
    assert partial_result['cost']['chart_dimension']==2 and partial_result['cost']['residual_clauses']==5
    print('non-affine partial hull, Gauss, terminal cap and original fallback passed')
