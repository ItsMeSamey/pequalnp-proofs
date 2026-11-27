from itertools import product
from collections import Counter
from event_affine_ie import solve
from event_ie_solver import solve as physical_solve
from padding_cnf import encode
from stage4_nonaffine import and_gate,codebooks as and_codes
from stage4_fixed_event import fixed_clique,record_codes

def verify(ds,cs,out,**opts):
    valid=[]
    for row in product(*ds.values()):
        w=dict(zip(ds,row))
        if all((w[u],w[v]) in rel for u,v,rel in cs): valid.append(w)
    expected={b:sum(w[out]==b for w in valid) for b in (0,1)}
    r=solve(ds,cs,out,**opts)
    assert r.get('counts')==expected,(r,expected)
    assert set(r['witnesses'])=={k for k,v in expected.items() if v}
    for k,w in r['witnesses'].items(): assert w in valid and w[out]==k

def generic():
    bits=(0,1)
    ds={k:bits for k in 'xyzp'}
    full=set(product(bits,repeat=2))
    eq=(('x','y',{(0,0),(1,1)}),)
    a=('x','z',full-{(0,0)})
    b=('y','z',full-{(0,0)})
    c=('y','p',full-{(0,0)})
    for cols in ((a,), (a,a), (a,b), (a,b,c), (a,b,c,('z','p',full-{(1,1)}))):
        verify(ds,eq+cols,'p')
    verify(ds,eq+(a,b,c,('x','x',set())),'p')
    for cap in ('omission_cap','branch_cap'):
        r=solve(ds,eq+(a,b,c),'p',**{cap:0})
        assert r['status']=='unknown' and 'counts' not in r
    verify(ds,eq+(a,b,c),'p',codebooks={k:{0:2,1:9} for k in 'xyz'})
    assert solve({i:bits for i in range(62)},[],0)['counts']=={0:1<<61,1:1<<61}
    print('repeated, coincident and overlapping exclusions; exact 62-bit count')

def physical(f,codes,expected,extra_ids=(),extra_occ=(),brute=True,period=False):
    from event_period_solver import solve as period_solve
    args=[f[k] for k in ('challenge','n','aliases','table','initial','bottom','outputs')]
    aliases=[(abs(a),int(a<0)) for a in f['aliases']]
    occ=tuple(f['occurrence_pins'])+tuple(extra_occ)
    ids=tuple(f['id_pins'])+tuple(extra_ids)
    pins=dict(ids);conflict=len(pins)!=len(set(ids))
    for i,b in occ:
        a,s=aliases[i]
        if pins.setdefault(a,b^s)!=b^s: conflict=True
    free=sorted({a for a,s in aliases}-pins.keys())
    def at(values):
        key=sum((values[a]^s)<<i for i,(a,s) in enumerate(aliases))
        raw=encode(f['challenge'],f['n'],key)
        q=f['initial']; stack=[f['bottom']]
        for ch in raw:
            act=f['table'][q,stack[-1],ch]
            q=act[0]
            if act[1]=='push': stack.append(act[2])
            if act[1]=='pop': stack.pop()
        return raw,key,int(f['outputs'][q])
    if brute:
        ref=Counter()
        if not conflict:
            for bits in product((0,1),repeat=len(free)):
                values={**pins,**dict(zip(free,bits))}
                ref[at(values)[2]]+=1
        assert {b:ref[b] for b in (0,1)}==expected
    opts=dict(codebooks=codes,occurrence_pins=occ,id_pins=ids,schedule=f['macro_schedule'])
    for fn in ([physical_solve,period_solve] if period else [physical_solve]):
        r=fn(*args,**opts)
        if fn==physical_solve: assert r.get('counts')==expected,(r.get('reason'),expected)
        support={b for b,c in expected.items() if c}
        assert {s['prediction'] for s in r['samples']}==support
        for sample in r['samples']:
            values=sample['underlying']
            assert all(values[a]==b for a,b in pins.items())
            assert at(values)==(sample['physical'],sample['key'],sample['prediction'])
    print('physical',len(free),expected,'brute',brute,'period',period)

def main():
    generic()
    f=and_gate()
    physical(f,and_codes,{0:3,1:1},period=True)
    physical(f,and_codes,{0:2,1:0},extra_ids=[(71,1)])
    physical(f,and_codes,{0:0,1:0},extra_occ=[(1,0),(1,1)])
    f=fixed_clique(5,paired=False)
    physical(f,record_codes,{0:256,1:256},period=True)
    f=fixed_clique(5,paired=True)
    physical(f,record_codes,{0:1<<18,1:1<<18},brute=False)
    names=sorted({abs(a) for a in f['aliases']}-{1,2003,2077})
    physical(f,record_codes,{0:1,1:1},extra_ids=[(a,0) for a in names])
    print('IE exact counts, source lifts, fixed XOR predictors and capped refusals passed')
if __name__=='__main__': main()
