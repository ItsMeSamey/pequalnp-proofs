"""Count either output of a cubic ANF with a recognized disjoint-volume tensor.

Monomials are variable-subset bit masks (0 = constant). Return None on recognition
failure. The solver uses the recovered block order; counts include all inputs.
"""
from itertools import combinations


def _apply(cols,x):
    v=0
    while x:
        low=x&-x
        v^=cols[low.bit_length()-1]
        x^=low
    return v


def _linear(rows,n):
    """Return one solution and a basis of the kernel, or None."""
    pivots={}
    for mask,rhs in rows:
        while mask:
            j=mask.bit_length()-1
            if j not in pivots:
                pivots[j]=(mask,rhs)
                break
            m,b=pivots[j]
            mask,rhs=mask^m,rhs^b
        if not mask and rhs:return None
    def lift(x,affine):
        for j,(m,b) in sorted(pivots.items()):
            x|=(((m&x).bit_count()^(b if affine else 0))&1)<<j
        return x
    return lift(0,True),[lift(1<<j,False) for j in range(n) if j not in pivots]


def _value(p,x):
    return sum(x&m==m for m in p)%2


def _pullback(p,cols):
    # A degree-three ANF is determined by evaluations at weights 0 through 3.
    n=len(cols)
    result=set()
    for d in range(4):
        for ids in combinations(range(n),d):
            x=sum(1<<j for j in ids)
            sub=x
            c=0
            while True:
                c^=_value(p,_apply(cols,sub))
                if not sub:break
                sub=(sub-1)&x
            if c:result.add(x)
    return result


def _tensor_rows(p,n):
    out=[[0]*n for _ in range(n)]
    for t in p:
        if t.bit_count()!=3:continue
        ids=[j for j in range(n) if t>>j&1]
        for a,b in combinations(ids,2):
            out[a][b]=out[b][a]=out[a][b]^(t^(1<<a)^(1<<b))
    return out


def _coordinates(p,n):
    tensor=_tensor_rows(p,n)
    rows=[(entry,0) for r in tensor for entry in r]
    _,rad=_linear(rows,n)
    # Row-reduce the radical. Unit vectors in its nonpivot positions give a complement.
    pivots={}
    for v in rad:
        while v:
            k=v.bit_length()-1
            if k not in pivots:
                pivots[k]=v
                break
            v^=pivots[k]
    comp=[1<<i for i in range(n) if i not in pivots]
    h=len(comp)
    if h%3:return None
    cubic=_pullback({m for m in p if m.bit_count()==3},comp)
    t=_tensor_rows(cubic,h)
    eq=[]
    for i in range(h):
        for j in range(h):
            for k in range(h):
                a=t[j][k]<<(h*i)
                eq.extend(((a^(t[i][k]<<(h*j)),0),(a^(t[i][j]<<(h*k)),0)))
    _,center=_linear(eq,h*h)
    if len(center)!=h//3:return None
    blocks=[list(1<<i for i in range(h))] if h else []
    for matrix in center:
        cols=[(matrix>>(h*j))&((1<<h)-1) for j in range(h)]
        new=[]
        for basis in blocks:
            subs=[]
            for eig in (0,1):
                val=[_apply(cols,v)^(v if eig else 0) for v in basis]
                eq=[(sum(((v>>i)&1)<<j for j,v in enumerate(val)),0) for i in range(h)]
                _,ker=_linear(eq,len(basis))
                if ker:subs.append([_apply(basis,w) for w in ker])
            if sum(map(len,subs))!=len(basis):return None
            new.extend(subs)
        blocks=new
    if any(len(b)!=3 for b in blocks):return None
    cols=[_apply(comp,w) for b in blocks for w in b]+rad
    new=_pullback(p,cols)
    if {m for m in new if m.bit_count()==3}!={7<<j for j in range(0,h,3)}:return None
    return h,new


def _integrate(p,n,h):
    p=p.copy()
    radical=((1<<n)-1)^((1<<h)-1)
    power=0
    while True:
        pair=next((t for t in p if (t&radical).bit_count()==2),None)
        if pair is None:break
        a=pair&-pair
        b=pair^a
        A=[t^a for t in p if t!=pair and t&a]
        B=[t^b for t in p if t!=pair and t&b]
        p={t for t in p if not t&pair}
        for x in A:
            for y in B:p.symmetric_difference_update((x|y,))
        power+=1
        radical^=pair
    checks=[]
    while radical:
        a=radical&-radical
        coef=[t^a for t in p if t&a]
        checks.append((sum(v for v in coef if v),int(0 in coef)))
        p={t for t in p if not t&a}
        power+=1
        radical^=a
    return p,checks,power


def _signed_dp(p,checks,h):
    if _linear(checks,h) is None:return 0,0
    # Representatives are actual encountered past assignments, cached per state.
    def classify(u,k):
        rows=[(m>>k,b^((m&u).bit_count()%2)) for m,b in checks]
        data=_linear(rows,h-k)
        if data is None:return None
        ref,ker=data
        def cross(v):
            v<<=k
            return _value(p,u^v)^_value(p,u)^_value(p,v)^int(0 in p)
        key=(tuple(b for m,b in rows),tuple(cross(v) for v in ker))
        return key,cross(ref)
    states={0:(((-1)**int(0 in p)),0,0)}
    peak=1
    for k in range(0,h,3):
        nxt={}
        for weight,u,oldnorm in states.values():
            for block in range(8):
                w=u^(block<<k)
                data=classify(w,k+3)
                if data is None:continue
                key,norm=data
                delta=_value(p,w)^_value(p,u)^oldnorm^norm
                prev,rep,repnorm=nxt.get(key,(0,w,norm))
                nxt[key]=(prev+weight*(-1)**delta,rep,repnorm)
        states=nxt
        peak=max(peak,len(states))
    return sum(a for a,_,_ in states.values()),peak


def count(q,monomials):
    if q<0:raise ValueError('negative input dimension')
    p=set()
    for m in monomials:
        if not isinstance(m,int) or m<0 or m>>q or m.bit_count()>3:
            raise ValueError('invalid cubic ANF mask')
        p.symmetric_difference_update((m,))
    prep=_coordinates(p,q)
    if prep is None:return None
    h,p=prep
    p,checks,power=_integrate(p,q,h)
    sign,peak=_signed_dp(p,checks,h)
    signed=sign<<power
    return dict(zero=((1<<q)+signed)//2,one=((1<<q)-signed)//2,
                signed=signed,blocks=h//3,radical=q-h,peak_states=peak)


def _selftest():
    from random import Random
    rng=Random(5827)
    systems=0
    def verify(n,p):
        nonlocal systems
        sol=count(n,p)
        assert sol is not None
        ones=sum(_value(p,x) for x in range(1<<n))
        assert sol['zero']==(1<<n)-ones and sol['one']==ones
        systems+=1
        return sol
    for n in range(10):
        for _ in range(9):
            blocks=rng.randrange(n//3+1)
            p={7<<(3*j) for j in range(blocks)}
            for d in range(3):
                for ids in combinations(range(n),d):
                    if rng.randrange(3)==0:p.add(sum(1<<j for j in ids))
            # Separate symbolic substitution implementing random affine shears.
            if n>=2:
                for _ in range(n*3):
                    i,j=rng.sample(range(n),2)
                    shift=rng.randrange(2)
                    old=p.copy()
                    for m in old:
                        if m>>i&1:
                            rest=m^(1<<i)
                            p.symmetric_difference_update((rest|(1<<j),))
                            if shift:p.symmetric_difference_update((rest,))
            sol=verify(n,p)
            assert sol['blocks']==blocks and sol['radical']==n-3*blocks
    for p in ({7,56,65,384,258,514},{7,56,64},{7,56,65,66,128,129,130}):
        verify(10,p)
    # Four blocks with an invertible six-bit interaction across their middle cut.
    wide={7,56,448,3584}|{(1<<i)|(1<<(i+6)) for i in range(6)}
    verify(12,wide)
    # Isolated radical drift forces an inconsistent equation, hence a balanced phase.
    assert verify(7,{7,56,64})['signed']==0
    bad={7,25}  # x0 times a nondegenerate quadratic on four other bits.
    assert count(5,bad) is None
    # Non-class with radical-free dimension six, so the dimension precheck passes.
    bad2={7,25,42}
    assert count(6,bad2) is None
    assert count(4,[7,7,1])['one']==8
    print(systems,'recognized transformed/structured systems; two declines and duplicate masks passed')


if __name__=='__main__':
    import argparse
    import json
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test',action='store_true')
    parser.add_argument('q',type=int,nargs='?')
    parser.add_argument('monomials',type=lambda s:int(s,0),nargs='*')
    args=parser.parse_args()
    if args.self_test:_selftest()
    elif args.q is None:parser.error('supply q and integer monomial masks, or --self-test')
    else:print(json.dumps(count(args.q,args.monomials)))
