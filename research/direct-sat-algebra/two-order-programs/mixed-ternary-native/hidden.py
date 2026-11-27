from random import Random
from itertools import combinations
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check import xor3
from solver import solve,chart,accepts_cnf,span

def fixture(m,copies,bad,seed):
    rng=Random(seed)
    rows=[];eq=[];targets=[];exterior=[];pairs=[]
    n=0
    for k in range(copies):
        p,q,r=n+1,n+2,n+3;n+=3;targets.append((p,q,r));exterior.extend((p,q))
        block=[]
        for i in range(m):
            a,b,e,f,g,c=range(n+1,n+7);n+=6
            exterior.extend((a,b));block.append((a,b))
            for triple in ((a,p,e),(b,q,f),(e,r,g),(g,f,c)):
                rows+=xor3(*triple);eq.append(triple)
            rows.append((a,rng.choice((-b,b)),rng.choice((-c,c))))
        pairs.append(block)
    for _ in range(3*m*copies):
        a,b=rng.sample(exterior,2)
        rows.append((a,rng.choice((b,-b))))
    if bad:
        a,b,c=[s[0] for s in pairs[0][:3]]
        for x,y in ((a,b),(b,c),(c,a)):rows.extend([(x,y),(-x,-y)])
    ids=list(range(1,n+1));rng.shuffle(ids)
    if seed==0:ids=list(range(1,n+1))
    def mapped(v):return (1 if v>0 else -1)*ids[abs(v)-1]
    raw=[tuple(mapped(v) for v in rng.sample(list(row),len(row))) for row in rows]
    rng.shuffle(raw)
    mask=lambda t:sum(1<<(mapped(v)-1) for v in t)
    return n,raw,[mask(t) for t in eq],[mask(t) for t in targets]

if __name__=='__main__':
    result=[]
    for copies in (1,2):
        for seed in range(16):
            for bad in (False,True):
                n,cs,linear,targets=fixture(3+(seed%3),copies,bad,seed)
                ans=solve(n,cs,b=copies,extract_arities=(3,),orient=True,exponent_cap=0)
                assert ans['status']==('unsat' if bad else 'sat') and all(t['method']=='2sat' for t in ans['cost']['cosets'])
                d,forms=chart(n,[(u,0) for u in linear])
                def normal(t):
                    y=0
                    while t:
                        b=t&-t;y ^= forms[b.bit_length()-1]>>1;t ^= b
                    return y
                required=[normal(t) for t in targets]
                assert span(ans['cost']['cover'])==span(required)
                rawset={f>>1 for f in forms}
                differences={a^b for a,b in combinations(rawset,2)}
                assert not any(t in rawset|differences for t in required)
                assert solve(n,cs,b=copies-1,extract_arities=(3,),orient=True,exponent_cap=0)['status']=='skip'
                if not bad:assert accepts_cnf(cs,ans['witness'])
                result.append(dict(seed=seed,copies=copies,n=n,status=ans['status'],cost=ans['cost']))
    print('64 hidden family controls: original-coordinate cover equality and no single/pair raw realization checked')
    open('hidden.json','w').write(json.dumps(result,indent=2)+'\n')
