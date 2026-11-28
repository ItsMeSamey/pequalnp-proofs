"""Check original sparse CNF models and the claimed one-coordinate cover."""
from itertools import product, combinations
from source_remote_pivot import solve

def fixture(m,no=False):
    w=10**9+7
    blocks=[tuple(100*i+j for j in (3,9,17)) for i in range(m)]
    rows=[]
    for a,b,c in blocks:
        rows.extend(((a,b,c),(-a,-b,-c),(-w,-a),(w,-b)))
    if no:
        a,b,c=blocks[0]
        rows.extend(tuple(sign*x for sign,x in zip(s,(a,b,c)))
                    for s in product((1,-1),repeat=3))
    return w,blocks,rows

def oracle(rows,pins):
    names=sorted({abs(x) for row in rows for x in row}|{i for i,b in pins})
    for values in product((0,1),repeat=len(names)):
        v=dict(zip(names,values))
        if all(v[i]==b for i,b in pins) and all(any(v[abs(x)]==(x>0) for x in row) for row in rows):
            return tuple(i for i in names if v[i])
    return None

def check(n,rows,pins=(),**kw):
    want=oracle(rows,pins)
    r=solve(n,rows,source_pins=pins,**kw)
    assert r['status']==('UNSAT' if want is None else 'SAT'),(r,want)
    if want is None: assert r['true_variables'] is None
    else:
        t=r['true_variables']
        assert tuple(sorted(set(t)))==t and all(1<=i<=n for i in t)
        t=set(t)
        assert all((i in t)==b for i,b in pins)
        assert all(any((abs(x) in t)==(x>0) for x in row) for row in rows)
    return r

def main():
    for no in (False,True):
        w,blocks,rows=fixture(3,no)
        triples={frozenset(map(abs,row)) for row in rows if len(row)==3}
        assert len(triples)==3 and sum(map(len,triples))==len(set.union(set(),*triples))
        assert all(not all(any(v in t for v in hs) for t in triples)
                   for hs in combinations(set.union(set(),*triples),2))
        r=check(w,rows)
        assert tuple(r['pivots'])==(w,),r
        for y in (0,1):
            check(w,rows,[(w,y)])
        print('connected',r['status'],'one pivot vs three source hits',r['metrics'])
    w,_,rows=fixture(3)
    for cap in ('discovery_cap','branch_cap'):
        r=solve(w,rows,**{cap:0})
        assert r['status']=='UNKNOWN' and r['true_variables'] is None and r['reason']==cap.replace('_',' ')
    check(w,rows,[(w,1),(w,0)])
    check(w,[],[(w,1)])
    check(w,[()])
    for n,rows,pins in ((-1,[],()),(1,[(0,)],()),(1,[(2,)],()),(w,[],[(w+1,0)]),(w,[],[(0,1)])):
        try: solve(n,rows,source_pins=pins)
        except ValueError: continue
        raise AssertionError('invalid source declaration accepted')
    print('SAT and UNSAT source replay, both fibres, cap and malformed sparse controls passed')
    w,_,rows=fixture(3)
    for pinned in (((w,1),),((w,0),(w,1))):
        ans=solve(w,rows,source_pins=(iter(p) for p in pinned))
        assert ans['status']==('SAT' if len(pinned)==1 else 'UNSAT')
        if len(pinned)==1:
            chosen=set(ans['true_variables']); assert w in chosen
            assert all(any((abs(x) in chosen)==(x>0) for x in row) for row in rows)
    print('one-shot nested source pins passed')
if __name__=='__main__': main()
