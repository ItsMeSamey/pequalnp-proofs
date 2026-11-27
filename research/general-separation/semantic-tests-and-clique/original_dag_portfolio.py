"""Finite corpus instrument. Enumerates full primary cube and ambient shear states."""
from random import Random

def val(row,u,z=0):
    a,f,c=row
    return ((a&u).bit_count()+(f&z).bit_count()+c)%2

def check(q,reads,output,upgrade=False):
    m=len(reads)//2
    raw=reads.copy()
    full=[]
    for x in range(1<<q):
        z=0
        for i in range(m):
            z |= (val(raw[2*i],x,z)&val(raw[2*i+1],x,z))<<i
        full.append(val(output,x,z))
    rows=reads+[output]
    n=q
    eqs=[]
    lift=list(range(1<<q))
    absorbed=0
    upgraded=False
    retained=0
    profile=[]
    for i in range(m):
        profile.append((retained,reverse(rows,i)))
        a,b=rows[:2]
        rows=rows[2:]
        assert not (a[1] or b[1])
        p=[val(a,u)&val(b,u) for u in range(1<<n)]
        if not a[0] or not b[0] or a[0]==b[0]:
            mask=sum((p[1<<j]^p[0])<<j for j in range(n))
            assert all(val((mask,0,p[0]),u)==p[u] for u in range(1<<n))
            rows=[(l^(mask if f>>i&1 else 0), f&~(1<<i), c^(p[0] if f>>i&1 else 0)) for l,f,c in rows]
            continue
        active=[u for u,bit in enumerate(p) if bit]
        accepted=[]
        strict=[]
        for v in range(1<<n):
            if val((a[0],0,0),v) or val((b[0],0,0),v):continue
            if any((mask&v).bit_count()%2 != (future>>i&1) for mask,future,c in rows):continue
            gradients=[]
            kappas=[]
            for e in eqs:
                delta=[e[u^v]^e[u] for u in range(1<<n)]
                grad=sum((delta[1<<j]^delta[0])<<j for j in range(n))
                allowed=grad in (0,a[0],b[0],a[0]^b[0])
                assert allowed==(len({delta[u] for u in active})==1)
                gradients.append(grad)
                kappas.append(delta[active[0]])
            if all(g in (0,a[0],b[0],a[0]^b[0]) for g in gradients):
                accepted.append((v,kappas))
            if not any(gradients):strict.append(v)
        if accepted:
            v,kappas=accepted[0]
            upgraded |= not strict and any(kappas)
            absorbed+=1
            eqs=[[bit^(k&pu) for bit,pu in zip(e,p)] for e,k in zip(eqs,kappas)]
            lift=[u^(v if p[u] else 0) for u in lift]
            rows=[(mask,f&~(1<<i),c) for mask,f,c in rows]
        else:
            retained+=1
            rows=[(mask|(((f>>i)&1)<<n),f&~(1<<i),c) for mask,f,c in rows]
            eqs=[e+e for e in eqs]+[p+[b^1 for b in p]]
            lift=[u|(p[u]<<n) for u in lift]
            n+=1
        assert set(lift)=={u for u in range(1<<n) if all(not e[u] for e in eqs)}
        assert len(set(lift))==len(lift)
    assert [val(rows[0],u) for u in lift]==full
    assert not upgrade or upgraded
    return profile+[(retained,1)]

def reverse(rows,start):
    def visit(j,used):
        if j<0:return 1
        mask=1<<(start+j)
        deps=rows[2*j][1]|rows[2*j+1][1]
        if used&mask:return visit(j-1,used)+visit(j-1,used|deps)
        return visit(j-1,used|(deps if rows[-1][1]&mask else 0))
    return visit(len(rows)//2-1,0)


def compact(q,g):
    live={q+len(g)-1}
    for j in reversed(range(len(g))):
        if q+j in live:live.update(g[j][1:])
    indices={i:i for i in range(q)}
    out=[]
    for i,(c,a,b) in enumerate(g,q):
        if i in live:
            indices[i]=q+len(out)
            out.append((c,indices[a],indices[b]))
    return out


def prune(q,g):
    while True:
        changed=False
        for i,(c,a,b) in enumerate(g,q):
            if c!=6:continue
            for x,y in ((a,b),(b,a)):
                if x>=q:continue
                reach=[j==x for j in range(q)]
                for j,(_,s,t) in enumerate(g,q):
                    reach.append(j!=i and (reach[s] or reach[t]))
                if reach[y] or reach[-1]:continue
                if i==q+len(g)-1:return [(12,x,x)]
                g=compact(q,[(h,x if s==i else s,x if t==i else t) for h,s,t in g])
                changed=True
                break
            if changed:break
        if not changed:return g


def normalize(q,g):
    vals=[2<<i for i in range(q)]
    rows=[]
    for c,a,b in g:
        u,v=vals[a],vals[b]
        k=c&1
        r=k^(u if (c>>2^k)&1 else 0)^(v if (c>>1^k)&1 else 0)
        if c.bit_count()%2:
            r^=2<<(q+len(rows)//2)
            rows.extend((u,v))
        vals.append(r)
    def row(r):return (r>>1&((1<<q)-1),r>>(q+1),r&1)
    return list(map(row,rows)),row(vals[-1])


def table(q,g):
    total=0
    for x in range(1<<q):
        v=[x>>i&1 for i in range(q)]
        for c,a,b in g:v.append(c>>(2*v[a]+v[b])&1)
        total|=v[-1]<<x
    return total


def analyze(q,gates):
    if not 1<=q<=8 or not 1<=len(gates)<=160:raise ValueError('size cap')
    if any(not(0<=c<16 and 0<=a<i and 0<=b<i) for i,(c,a,b) in enumerate(gates,q)):
        raise ValueError('invalid gate')
    g=compact(q,gates)
    reads,out=normalize(q,g)
    if q+len(reads)//2>15:raise ValueError('ambient dimension cap 15')
    tt=table(q,g)
    anf=tt
    for j in range(q):
        high=sum(1<<x for x in range(1<<q) if x>>j&1)
        anf^=(anf<<(1<<j))&high
    deg=max((x.bit_count() for x in range(1<<q) if anf>>x&1),default=0)
    normalized=0
    for x in range(1<<q):
        z=0
        for j,(a,b) in enumerate(zip(reads[::2],reads[1::2])):
            z|=(val(a,x,z)&val(b,x,z))<<j
        normalized|=val(out,x,z)<<x
    assert normalized==tt
    profile=check(q,reads,out)
    gg=prune(q,g)
    assert table(q,gg).bit_count()==tt.bit_count()
    after=check(q,*normalize(q,gg)) if gg!=g else profile
    def best(p):return min(((1<<f)*t,i) for i,(f,t) in enumerate(p))
    from math import comb
    buckets=[{tt>>x&1 for x in range(1<<q) if x.bit_count()==w} for w in range(q+1)]
    symmetric=all(len(b)==1 for b in buckets)
    if symmetric:assert sum(comb(q,w) for w,b in enumerate(buckets) if 1 in b)==tt.bit_count()
    from original_dag_quadratic import count
    gauss=count(q,g,cap=128)
    if gauss is not None:assert gauss[0]==tt.bit_count()
    return dict(gauss=gauss,weight=weight(q,g,tt),q=q,live=len(g),q_plus_live=q+len(g),products=len(profile)-1,truth=hex(tt),
                ones=tt.bit_count(),degree=deg,quadratic_by_full_cube=deg<=2,symmetric_by_full_cube=symmetric,
                f=profile[-1][0],T=profile[0][1],mixed=best(profile),removed=len(g)-len(gg),
                after_mixed=best(after),cuts=profile)

def corpus():
    from itertools import combinations
    q=5
    def builder():
        g=[]
        def add(c,a,b):
            g.append((c,a,b))
            return q+len(g)-1
        def xor(items):
            a,*tail=items
            for b in tail:a=add(6,a,b)
            return a
        return g,add,xor
    g,add,xor=builder()
    forms=[xor([j for j in range(q) if m>>j&1]) for m in (29,23,19,15,26)]
    xor([add(8,forms[i],forms[(i+1)%5]) for i in range(5)])
    yield 'dense-coded',q,g
    g,add,xor=builder()
    r=[3,4]; ds=[]
    for i,(a,b) in enumerate(combinations(range(3),2)):
        d=add(8,a,b)
        ds.append(d)
        j=i%2
        r[j]=add(6,r[j],add(8,d,r[1-j]))
    add(8,xor(ds),r[0])
    yield 'alternating',q,g
    g,add,xor=builder()
    a=0
    for j in range(1,9):a=add(8,a,j%q)
    yield 'chain',q,g
    g,add,xor=builder()
    add(8,add(6,0,add(8,1,2)),add(6,3,4))
    yield 'postdominator',q,g
    q=3
    g,add,xor=builder()
    r=list(range(q))
    for i in range(5):
        t=i%q
        r[t]=add(6,r[t],add(8,r[(t+1)%q],r[(t+2)%q]))
    a=add(8,xor(r),r[0])
    for i in range(3):a=add(8,a,r[i])
    yield 'interior-cut',q,g


def weight(q,g,truth):
    from affine_weight_portfolio import affine_weight_count
    result=affine_weight_count(q,g,term_cap=128)
    if result is not None:assert result['count']==truth.bit_count()
    return result


def weight_control():
    from itertools import combinations
    q=5
    g=[]
    def add(c,a,b):
        g.append((c,a,b))
        return q+len(g)-1
    forms=[0]+[add(6,j-1,j) for j in range(1,q)]
    triples=[add(8,add(8,a,b),c) for a,b,c in combinations(forms,3)]
    last=triples[0]
    for term in triples[1:]:last=add(6,last,term)
    tt=table(q,g)
    result=weight(q,g,tt)
    assert result and result['dual_dimension']==0
    return dict(name='all-triples',q=q,gates=g,live=len(g),q_plus_live=q+len(g),
        truth=hex(tt),ones=tt.bit_count(),weight=result,shear='skipped: q+products=25 exceeds cap 15')


if __name__=='__main__':
    import json
    rng=Random(48103)
    print(json.dumps(dict(seed=48103,pool_size=96,q_cap=8,original_gate_cap=160,ambient_cap=15,term_cap=128)))
    print(json.dumps(weight_control()))
    pool=[]
    for name,q,g in corpus():
        print(json.dumps(dict(name=name,gates=g,**analyze(q,g))))
    for i in range(96):
        q=4
        g=[]
        for j in range(5+i%5):
            g.append((rng.choice((8,6,14,7,9,11)),rng.randrange(q+j),rng.randrange(q+j)))
        stats=analyze(q,g)
        if i<4:print(json.dumps(dict(name=f'random-{i}',gates=g,**stats)))
        if stats['degree']>2 and stats['after_mixed'][0]>=4 and stats['weight'] is None and (stats['gauss'] is None or stats['gauss'][-1]>=2):
            pool.append((stats['live'],i,g,stats))
    if pool:
        _,i,g,stats=min(pool)
        print(json.dumps(dict(name='smallest-pool-resistant',index=i,eligible=len(pool),gates=g,**stats)))
