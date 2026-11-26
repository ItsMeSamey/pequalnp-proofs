"""Rooted binary projective closure, with local proof records and replay."""
from functools import lru_cache
from itertools import combinations
from time import monotonic


def reduce_row(v,system):
    bit=0
    for k,(r,b) in sorted(system.items(),reverse=True):
        if v>>k&1:
            v^=r
            bit^=b
    return v,bit


def insert(system,v,b):
    v,delta=reduce_row(v,system)
    if not v:return b==delta
    system[v.bit_length()-1]=(v,b^delta)
    return True


def basis(rows):
    s={}
    for v in rows:insert(s,v,0)
    keys=sorted(s)
    for i,k in enumerate(keys):
        v=s[k][0]
        for j in keys[:i]:
            if v>>j&1:v^=s[j][0]
        s[k]=(v,0)
    return tuple(s[k][0] for k in keys)


def span(B):
    values=[0]
    for x in B:values.extend([x^v for v in values])
    return values


@lru_cache(None)
def masks(k):
    allbits=(1<<(1<<(2*k)))-1
    par=[sum(1<<f for f in range(1<<(2*k)) if (f&v).bit_count()%2) for v in range(1<<(2*k))]
    nonzero=[par[v]|par[v<<k] for v in range(1<<k)]
    return allbits,par,nonzero


def table(B,d,points,system):
    k=len(B)
    vals=span(B)
    forms=(*B,*(v<<d for v in B))
    allbits,par,nonzero=masks(k)
    possible=allbits
    dependencies={}
    for i,v in enumerate(forms):
        rem,rhs=reduce_row(v,system)
        coeff=1<<i
        while rem and rem.bit_length() in dependencies:
            w,h,c=dependencies[rem.bit_length()]
            rem^=w
            rhs^=h
            coeff^=c
        if rem:dependencies[rem.bit_length()]=(rem,rhs,coeff)
        else:possible &= par[coeff] if rhs else allbits^par[coeff]
    legal=possible
    for i,v in enumerate(vals):
        if v in points:legal &= nonzero[i]
    return legal,possible,vals,forms


def deductions(B,d,points,system):
    legal,possible,vals,forms=table(B,d,points,system)
    if not legal:return None
    allbits,par,nonzero=masks(len(B))
    newpts=[v for i,v in enumerate(vals) if v and v not in points and not legal&~nonzero[i]]
    eq=[]
    if legal!=possible:
        first=(legal&-legal).bit_length()-1
        for i,pm in enumerate(par[1:],1):
            rhs=(first&i).bit_count()%2
            bad=(allbits^pm) if rhs else pm
            if legal&bad or not possible&bad:continue
            v=0
            for j,w in enumerate(forms):
                if i>>j&1:v^=w
            rem,_=reduce_row(v,system)
            if rem:
                eq.append((v,rhs))
                if not insert(system,v,rhs): raise ValueError("inconsistent local consequence")
    points.update(newpts)
    return eq,newpts


def start(d,original,root):
    p=set(original)
    a,b=root
    if not (0<a<1<<d and 0<b<1<<d and a!=b and {a,b,a^b}<=p):
        raise ValueError("root must be a line of three required nonzero points")
    if any(v<0 or v>=1<<d for v in p):raise ValueError("point out of range")
    s={}
    for v,rhs in ((a,1),(a<<d,0),(b,0),(b<<d,1)):
        if not insert(s,v,rhs): raise ValueError("inconsistent root normalization")
    return p,s


def close(d,original,root,*,seconds=None):
    started=monotonic()
    p,s=start(d,original,root)
    initial=sorted(set(original))
    spaces=sorted({basis(t) for t in combinations(initial,min(4,len(initial)))},key=lambda B:(len(B),B))
    log=[]
    sweeps=0
    while True:
        sweeps+=1
        old=len(s),len(p)
        for B in spaces:
            if seconds is not None and monotonic()-started>seconds:
                return 'BUDGET',log,len(s),len(p),len(spaces),sweeps
            changes=deductions(B,d,p,s)
            if changes is None:
                log.append((B,None))
                return 'UNSAT',log,len(s),len(p),len(spaces),sweeps
            if any(changes):log.append((B,changes))
        if old==(len(s),len(p)):return 'STABLE',log,len(s),len(p),len(spaces),sweeps


def replay(d,original,root,log):
    p,s=start(d,original,root)
    for j,(B,changes) in enumerate(log):
        if len(B)>4 or any(not 0<v<1<<d for v in B) or len(basis(B))!=len(B):return False
        legal,_,vals,forms=table(B,d,p,s)
        if changes is None:return not legal and j==len(log)-1
        if not legal:return False
        eq,new=changes
        k=len(B)
        _,par,nz=masks(k)
        for v in new:
            if v not in vals or legal&~nz[vals.index(v)]:return False
        for v,b in eq:
            bits=(1<<d)-1
            if v<0 or v>>(2*d) or (v&bits) not in vals or (v>>d) not in vals or b not in (0,1):return False
            form=vals.index(v&bits)|(vals.index(v>>d)<<k)
            if legal&( ~par[form] if b else par[form]):return False
            if not insert(s,v,b):return False
        p.update(new)
    return True


def replay_unsat(d,original,root,log):
    """Accept only a derivation ending in a replayed empty local table."""
    return bool(log) and log[-1][1] is None and replay(d,original,root,log)
