"""Verify the case analysis and hard-query bound against explicit lobe tables."""
from itertools import combinations
from collections import Counter
from random import Random
from check_cut_guards import table,lobe

ALL=set(range(16))
def plus(A,B):
    return {a^b for a in A for b in B}

def recover(S,V,rng):
    witnesses=set();missing=set()
    for a,b in combinations(sorted(V),2):
        options=sorted({a,b}&S)
        if options:witnesses.add(rng.choice(options))
        else:missing.update((a,b))
    if missing:
        assert S&V==V-missing==witnesses
        return True,witnesses
    assert len(V-witnesses)<=1
    return False,witnesses

def check(rng,stats):
    A,L=lobe(rng);B,R=lobe(rng)
    R[0]=0;s=L[0]
    f=table(A,L);g=table(B,R)
    A0={z for x,z in f.items() if not x&1};A1={z for x,z in f.items() if x&1}
    B0={z for x,z in g.items() if not x&1};B1={z for x,z in g.items() if x&1}
    U,V=plus(A0,A0),plus(B0,B0)
    assert U==plus(U,U) and V==plus(V,V)
    if len(U)==1 or len(V)==1:
        stats["zero open"]+=1
        return
    fa,aw=recover(A0,ALL,rng);fb,bw=recover(B0,ALL,rng)
    for p in range(16):
        if p in plus(aw,bw):
            assert p in plus(A0,B0)
            continue
        assert fa and fb and p not in plus(A0,B0)
        W=plus({s},U)&plus({p},V)
        true=bool(A1&plus({p},B1))
        X,Y=A1&W,plus({p},B1)&W
        target_sets=[X,Y]
        called=[0,0]
        def lookup(side,a):
            called[side]+=1
            local=a^(p if side else 0)
            rows,labels=(B,R) if side else (A,L)
            shifted=labels[:];shifted[0]^=p^local
            ok=p in table(rows,shifted).values()
            assert ok==(a in target_sets[side])
            return ok
        def partial(side):
            assert len(W)>=2
            T=target_sets[side]
            for a,b in combinations(sorted(W),2):
                h=a^b;opposite,zero,one=(A0,B0,B1) if side else (B0,A0,A1)
                witness=next(t for t in opposite if t^h in opposite)
                c=p^witness
                assert c not in zero and c^h not in zero
                score=a^(p if side else 0)
                assert bool({a,b}&T)==bool({score,score^h}&one)
            return recover(T,W,rng)
        if not W:answer=False
        elif len(W)==1:
            a=next(iter(W));answer=lookup(0,a) and lookup(1,a)
        elif len(W)==2:
            if not X or not Y:answer=False
            else:
                x=rng.choice(sorted(X));y=rng.choice(sorted(Y))
                answer=x==y or lookup(0,y) or lookup(1,x)
        else:
            ex,x=partial(0);ey,y=partial(1)
            if x&y:answer=True
            elif ex and ey:answer=False
            elif ex:answer=bool(x) and lookup(1,next(iter(x)))
            elif ey:answer=bool(y) and lookup(0,next(iter(y)))
            else:raise AssertionError("dense witnesses must overlap")
        assert answer==true and max(called)<=1
        stats[len(W),sum(called)]+=1

if __name__=="__main__":
    rng=Random(4741);stats=Counter()
    for _ in range(700):check(rng,stats)
    print("700 lobe pairs passed",dict(stats))
