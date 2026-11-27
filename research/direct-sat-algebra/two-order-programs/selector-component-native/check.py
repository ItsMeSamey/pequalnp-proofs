from itertools import product
from pathlib import Path
from random import Random
import json,sys
from projection import solve,accepts_cnf
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'selector-variable-compiler'))
from compiler import compile_cnf,decode

def run(n,rows,label,seed,**options):
    N,physical,metadata=compile_cnf(n,rows)
    rng=Random(seed)
    perm=list(range(1,N+1));rng.shuffle(perm)
    raw=[tuple(perm[abs(l)-1]*(1 if l>0 else -1) for l in row) for row in physical]
    rng.shuffle(raw)
    result=solve(N,raw,**options)
    if result['status']=='sat':
        assert accepts_cnf(raw,result['witness'])
        original=sum(((result['witness']>>(j-1))&1)<<i for i,j in enumerate(perm))
        word=decode(original,metadata)
        assert accepts_cnf(rows,word)
        result['decoded_source']=word
    print(label,n,N,result['status'],result['reason'],result['cost'].get('table_probes'),flush=True)
    return dict(label=label,**result)

if __name__=='__main__':
    out=[]
    for n,target in [(5,31),(6,37),(8,219)]:
        rows=[]
        for j in range(n):
            lit=(j+1)*(1 if target>>j&1 else -1)
            a=(j+1)%n+1;b=(j+2)%n+1
            rows += [(lit,sa*a,sb*b) for sa,sb in product((-1,1),repeat=2)]
        result=run(n,rows,'signed units',691+n)
        assert result['decoded_source']==target and result['cost']['join']=='unary'
        out.append(result)
    hard=[tuple((-v if bit else v) for v,bit in zip(scope,bits))
          for scope,bits in [((1,2,3),(0,0,0)),((2,3,4),(1,1,1))]]
    # A positive 3-clause and a negative 3-clause have no common affine/meet/majority class.
    hard_result=run(4,hard,'mixed projected join',313)
    assert hard_result['status']=='skip'
    out.append(hard_result)
    fallback=run(4,hard,'bounded enumeration',313,fallback_limit=16)
    assert fallback['status']=='sat' and fallback['cost']['fallback_evaluations']>0
    out.append(fallback)
    positive=[tuple(-v if bit else v for v,bit in zip((1,2,3),z)) for z in product((0,1),repeat=3)]
    empty=run(3,positive,'empty grouped intersection',37)
    assert empty['status']=='unsat';out.append(empty)
    for opts in [dict(scope_cap=2),dict(table_cap=2)]:
        cap=run(4,hard,'resource cap',313,**opts)
        assert cap['status']=='skip';out.append(cap)
    open('receipt.json','w').write(json.dumps(out,indent=2)+'\n')
