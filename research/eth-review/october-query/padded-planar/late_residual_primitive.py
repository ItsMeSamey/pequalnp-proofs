"""Weighted violation-word recovery from exact candidate scores for one fixed prefix."""
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce


def primitive(p):
    scale=reduce(lcm,(c.denominator for c in p),1)
    values=[int(c*scale) for c in p]
    content=reduce(gcd,values,0)
    return [F(v//content) for v in values]


def linear(A,b):
    a=[list(map(F,row))+[F(y)] for row,y in zip(A,b)]
    for j in range(len(a)):
        k=next((k for k in range(j,len(a)) if a[k][j]),None)
        if k is None: raise ValueError("singular system")
        a[k],a[j]=a[j],a[k]
        a[j]=[v/a[j][j] for v in a[j]]
        for k in range(len(a)):
            if k!=j:
                t=a[k][j]
                a[k]=[v-t*w for v,w in zip(a[k],a[j])]
    return [row[-1] for row in a]


def roots(p,m):
    """Sturm bisection on half-integer boundaries around possible integer words."""
    seq=[primitive(p),primitive([i*p[i] for i in range(1,len(p))])]
    while True:
        a=seq[-2].copy()
        b=seq[-1]
        while len(a)>=len(b):
            shift=len(a)-len(b)
            v=a[-1]/b[-1]
            for j,c in enumerate(b): a[j+shift]-=v*c
            while a and not a[-1]: a.pop()
        if not a: break
        seq.append(primitive([-c for c in a]))
    def variation(x):
        signs=[]
        for q in seq:
            v=F(0)
            for c in reversed(q): v=v*x+c
            if v: signs.append(v>0)
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    hi=(1<<m)-1
    st=[(1,hi,variation(F(1,2)),variation(F(2*hi+1,2)))]
    out=[]
    while st:
        lo,hi,a,b=st.pop()
        if a==b: continue
        if lo==hi:
            out.append(lo)
            continue
        mid=(lo+hi)//2
        c=variation(F(2*mid+1,2))
        st.extend([(mid+1,hi,c,b),(lo,mid,a,c)])
    return sorted(out)


def recover(m,P,models,score,*,max_atoms,work_cap):
    """Return (true model count,{positive word:multiplicity}) or None at a cap.
    models=None uses shifted moments. Work cap counts coefficient updates and oracle calls.
    """
    if min(m,P,max_atoms,work_cap)<0 or models is not None and models<0: raise ValueError('negative input')
    if work_cap<1: return None
    base=score(0)
    if models is not None and base<models: raise ValueError('inconsistent model count')
    if not m or base==0 or models==base: return base,{}
    shift=int(models is None)
    mass=base-(models or 0)
    coefs={0:1}
    cache={0:mass}
    moments=[] if shift else [mass]
    work=1
    for k in range(1,min(P,2*min(max_atoms,mass)+shift)+1):
        work+=len(coefs)*(m+1)
        if work>work_cap: return None
        nxt={}
        for h,a in coefs.items():
            nxt[h]=nxt.get(h,0)+a*((1<<m)-1)
            for j in range(m):
                mask=h^(1<<j)
                nxt[mask]=nxt.get(mask,0)-(a<<j)
        coefs={h:a for h,a in nxt.items() if a}
        value=0
        for h,a in coefs.items():
            if h not in cache:
                work+=1
                if work>work_cap: return None
                assert h.bit_count()<=P
                cache[h]=2*score(h)-base-(models or 0)
            value+=a*cache[h]
        v,rem=divmod(value,1<<k)
        if rem: raise ValueError('nonintegral moment')
        moments.append(v)
        if shift and k==1 and v==0: return base,{}
        if k<=shift or (k-shift)%2: continue
        s=(k-shift)//2
        q=linear([moments[i:i+s] for i in range(s)],[-moments[i+s] for i in range(s)])+[F(1)]
        if sum(q[i]*q[j]*moments[i+j] for i in range(s+1) for j in range(s+1)): continue
        vals=roots(q,m)
        if len(vals)!=s or any(sum(c*v**i for i,c in enumerate(q)) for v in vals): raise ValueError('invalid roots')
        ws=linear([[v**i for v in vals] for i in range(s)],moments[:s])
        if shift: ws=[w/v for w,v in zip(ws,vals)]
        if any(w.denominator!=1 or w<=0 for w in ws): raise ValueError('invalid multiplicity')
        return base-int(sum(ws)),dict(zip(vals,map(int,ws)))
    return None


def candidate(models,atoms,mask):
    return models+sum(w for v,w in atoms.items() if (v&mask).bit_count()%2==0)
