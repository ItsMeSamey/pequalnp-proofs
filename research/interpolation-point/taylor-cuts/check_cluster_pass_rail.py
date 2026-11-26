"""Check envelope ranks by direct enumeration of all local prefix assignments."""
from itertools import product
from random import Random
from cluster_pass_rail import decide_clusters, _prefix_levels, _observable_pivots
from gram_pass_rail import prepare_passes
from check_finite_pass_rail import rank


def perms(d, passes, x, chosen):
    def apply(gates,s):
        for lit,a,b in gates:
            if abs(lit) in chosen:
                s=(b if (x>>(abs(lit)-1)&1)^(lit<0) else a)[s]
        return s
    return tuple(tuple(apply(gates,s) for s in range(d)) for _,gates in passes)


def check(n,d,passes,order,sizes,p,start,closing,trace=False):
    groups=[];k=0
    for size in sizes:
        groups.append(range(k,k+size));k+=size
    ans,pr,sr=decide_clusters(n,d,passes,order,sizes,prime=p,start=start,closing=closing,promised_trace=trace)
    def fixed(x,s):
        for perm in perms(d,passes,x,set(order)):
            s=perm[s]
        return closing[s]
    starts=range(d) if start is None else (start,)
    accepted={(x,s) for x in range(1<<n) for s in starts if fixed(x,s)==s}
    assert (ans in accepted if accepted else ans is None)
    _,ident,dirs,local=prepare_passes(n,d,passes,order)
    levels,_=_prefix_levels(order,ident,dirs,local,groups,p,None)
    peak=0
    for i in range(n+1):
        left=[perms(d,passes,x,set(order[:i])) for x in range(1<<n)]
        tails=set(perms(d,passes,x,set(order[i:])) for x in range(1<<n))
        choices=[set(tuple(t[j] for j in g) for t in left) for g in groups]
        cols=[]
        for tail in tails:
            col=[]
            for pick in product(*choices):
                pre=sum(pick,())
                diag=[]
                for s in starts:
                    t=s
                    for j,(forward,_) in enumerate(passes):
                        t=tail[j][pre[j][t]] if forward else pre[j][tail[j][t]]
                    diag.append(int(closing[t]==s))
                col.extend([sum(diag)%p] if trace else diag)
            cols.append(col)
        independent=rank(cols,p)
        assert len(_observable_pivots(list(tails),levels[i],groups,dirs,ident,closing,p,start,trace,None))==independent
        peak=max(peak,independent)
    assert peak==sr
    return pr,sr


if __name__=='__main__':
    rng=Random(7149)
    for _ in range(100):
        n=rng.randrange(1,4);d=rng.randrange(2,4);order=rng.sample(range(1,n+1),n)
        passes=[];sizes=[]
        for j in range(rng.randrange(4)):
            if j==0 or rng.randrange(2):sizes.append(1)
            else:sizes[-1]+=1
            f=rng.choice((False,True))
            gates=[(v*rng.choice((-1,1)),rng.sample(range(d),d),rng.sample(range(d),d))
                   for v in (order if f else reversed(order)) if rng.randrange(4)]
            passes.append((f,gates))
        check(n,d,passes,order,sizes,rng.choice((2,3,5)),rng.choice([None,rng.randrange(d)]),rng.sample(range(d),d))
    n=20;d=3;e=tuple(range(d));t=(1,0,2);rho=(1,2,0)
    passes=[(True,[(v,e,t)]) for v in range(1,n+1) for _ in range(2)]
    assert decide_clusters(n,d,passes,range(1,n+1),[2]*n,closing=rho)==(None,2,0)
    w,pr,sr=decide_clusters(n,d,passes,range(1,n+1),[2]*n)
    assert w==(0,0) and (pr,sr)==(2,1)
    e=tuple(range(5));rho=(1,2,3,4,0);inv=(4,0,1,2,3)
    for start in (None,3):
        check(2,5,[(True,[(2,e,rho)])],[1,2],[1],2,start,inv,trace=start is None)
    print('100 random cluster envelopes checked at every cut against dense ranks; 20 inverse-pair clusters and even Barrington accepting inputs passed')
