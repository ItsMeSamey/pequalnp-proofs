from random import Random
from pathlib import Path
import importlib.util
from two_state_other_order import solve,value
from two_order_semantic_labels import recognize,intersection

def remove_dead(p):
    initial,layers=p
    return ([2]*(len(layers)+1),1<<initial if initial<2 else 0,
            [tuple(tuple(1<<t[s][b] if t[s][b]<2 else 0 for s in (0,1)) for b in (0,1)) for _,t in layers],3),[v for v,_ in layers]

if __name__=='__main__':
    rng=Random(815)
    for _ in range(280):
        n=rng.randrange(8);first=list(range(n));other=first.copy()
        rng.shuffle(first);rng.shuffle(other)
        d=[rng.randrange(1,3) for i in range(n+1)];w=[rng.randrange(5) for i in range(n+1)]
        a=(d,1<<rng.randrange(d[0]),[tuple(tuple(1<<rng.randrange(b) for _ in range(c)) for x in (0,1)) for c,b in zip(d,d[1:])],rng.getrandbits(d[-1]))
        b=(w,rng.getrandbits(w[0]),[tuple(tuple(rng.getrandbits(b) for _ in range(c)) for x in (0,1)) for c,b in zip(w,w[1:])],rng.getrandbits(w[-1]))
        ok=[x for x in range(1<<n) if value(a,first,x) and value(b,other,x)]
        for r in (solve(a,first,b,other),intersection(b,other,a,first)):
            assert r['status']==('sat' if ok else 'unsat')
            if ok:assert r['witness'] in ok
        det,rec=recognize(b,other)
        if det is None:
            cut=rec['cut']
            signatures={tuple(value(b,other,word|sum(((s>>j)&1)<<v for j,v in enumerate(other[cut:]))) for s in range(1<<(n-cut))) for word in rec['prefixes']}
            assert len(signatures)==3
        else:assert all(value(b,other,x)==value(det,other,x) for x in range(1<<n))
    path=Path(__file__).resolve().parents[1]/'direct-sat-algebra/check_two_order_programs.py'
    spec=importlib.util.spec_from_file_location('two_orders_source',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    for clauses in [[(1,),(-1,)],[(1,2),(-1,2)],[(1,-1),(-2,)],[()]]:
        vs,a,b=mod.compile_programs(2,clauses)
        ap,ao=remove_dead(a);bp,bo=remove_dead(b)
        expected={sum(((x>>v)&1)<<i for i,v in enumerate(vs)) for x in range(4) if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)}
        assert expected=={x for x in range(1<<len(vs)) if value(ap,ao,x) and value(bp,bo,x)}
        assert solve(ap,ao,bp,bo)['status']=='skip'
    print('280 exhaustive two-order pairs and semantic-label checks; four exact partial controls')
