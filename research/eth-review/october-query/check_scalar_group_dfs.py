from collections import defaultdict
from itertools import product
from math import prod
from check_group_budget import kernel
from scalar_group_dfs import evaluate


def fixture(edges,t,zeta,p,sign):
    mod=1<<p
    gs=sorted(set(sum((list(e) for e in edges),[])))
    modes=[(e[1-s],e[s],1,1) for e in edges for s in (0,1)]
    W=[kernel(t,zeta,p,d) for d in (-1,0,1)]
    tables={}
    for g in gs:
        rr=[i for i,(u,v,_,_) in enumerate(modes) if v==g]
        cc=[i for i,(u,v,_,_) in enumerate(modes) if u==g]
        table={}
        for sel in product((0,1),repeat=len(rr+cc)):
            chosen={j for j,v in zip(rr+cc,sel) if v}
            total=0
            for x in (0,1):
                if not x and chosen.intersection(cc):
                    continue
                # Sum clause-row factors over all Y, subtract sole falsifying Y.
                value=int(not chosen.intersection(rr))
                bad=1
                for j in rr:
                    y=(sign>>j)&1
                    local=W[2 if j%2==0 else 0]*x
                    bad*=(2*y-1)*W[1] if j in chosen else (local if y else 1-local)
                total+=value-bad
            table[sel]=total%mod
        tables[g]=(rr+cc,table)
    def child(g,b):
        ix,tab=tables[g]
        return tab[tuple(b[j] for j in ix)]
    direct=0
    for word in product((0,1),repeat=len(gs)):
        x=dict(zip(gs,word))
        value=1
        for g in gs:
            bad=1
            for j,(source,target,_,_) in enumerate(modes):
                if target==g:
                    z=W[1]*x[source]+W[2 if j%2==0 else 0]*x[target]
                    bad*=z if (sign>>j)&1 else 1-z
            value*=1-bad
        direct+=value
    return gs,modes,child,direct%mod


def main():
    stats=defaultdict(lambda:[0,0,0,0])
    count=0
    for edges in [[(0,1),(1,2),(2,3)],[(0,1),(1,2),(2,3),(3,0)],[(0,1),(0,2),(0,3)]]:
        for t,z,p,sign in product((-1,1),(-1,1,2),(3,5,9),(0,37)):
            mod=1<<p
            ring=(0,1,lambda a,b:(a+b)%mod,lambda a,b:(a*b)%mod)
            gs,modes,child,direct=fixture(edges,t,z,p,sign)
            vals={}
            for method in ('literal','histogram','scalar'):
                vals[method],w=evaluate(gs,modes,p,child,ring,method)
                v=stats[method]
                v[0]+=w.adds; v[1]+=w.muls; v[2]+=w.leaf_calls
                v[3]=max(v[3],w.peak)
            assert vals['literal']==vals['histogram']
            assert sum(vals['literal'])%mod==vals['scalar']==direct
            def mark(j):
                return tuple(int(k==j) for k in range(p))
            def add(a,b):
                return tuple((x+y)%mod for x,y in zip(a,b))
            def mul(a,b):
                return tuple(sum(a[i]*b[k-i] for i in range(k+1))%mod for k in range(p))
            tagged,_=evaluate(gs,modes,p,lambda g,b:(child(g,b),)+(0,)*(p-1),
                              ((0,)*p,mark(0),add,mul),'scalar',mark)
            assert list(tagged)==vals['literal']
            count+=1
    # Two siblings may independently spend one, with P=2. Without target
    # divisibility their overweight product survives and breaks the identity.
    modes=[(0,1,1,1),(2,3,1,1)]
    ring=(0,1,lambda a,b:(a+b)%4,lambda a,b:(a*b)%4)
    kw=((0,1,2,3),modes,2,lambda g,b:1,ring)
    assert sum(evaluate(*kw,'literal')[0])%4==3
    assert evaluate(*kw,'scalar')[0]==0
    # Full source-sized group tree; empty groups do not
    # change the monitored four native factors; neutral empty groups equal 1.
    gs,modes,ch,d=fixture([(0,1),(1,2),(2,3)],1,1,9,0)
    scale=16
    sparse=[(scale*u,scale*v,w,k) for u,v,w,k in modes]
    ring=(0,1,lambda a,b:(a+b)%512,lambda a,b:(a*b)%512)
    val,w=evaluate(list(range(64)),sparse,9,
                   lambda g,b:ch(g//scale,b) if g%scale==0 else 1,ring)
    assert val==d
    print(count, 'four-group fixtures; totals [adds,muls,child calls,peak result slots]')
    for method,v in stats.items(): print(method,v)
    print('64-group scalar',val,w)
if __name__=='__main__':
    main()
