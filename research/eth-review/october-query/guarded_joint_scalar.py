"""Exact supplied guarded cubic A-child scalar on balanced physical-coordinate cuts."""
from collections import Counter

def echelon(rows):
    p={}
    for x in rows:
        while x:
            i=x.bit_length()-1
            if i not in p:
                p[i]=x
                break
            x^=p[i]
    return p

def reduce_word(x,p):
    for i in sorted(p,reverse=True):
        if x>>i&1: x^=p[i]
    return x

class Overflow(Exception): pass

def scalar(n,clauses,rows,trial,*,budget,fallback=None):
    """Optional fallback() returns (actual prefix count, signed character sum)."""
    cs=tuple(tuple(c) for c in clauses)
    q=len(cs)
    rows=tuple(rows)
    if budget<0 or any(x<0 or x>=1<<q for x in (*rows,trial)): raise ValueError('invalid input')
    units=[i for i,c in enumerate(cs) if len(c)==1]
    cnt=Counter(x for c in cs for x in c)
    if len(units)!=1 or any(x<=0 or x>n for x in cnt): return dict(status='unsupported')
    guard=units[0]
    if cnt[cs[guard][0]]!=1: return dict(status='unsupported')
    spins={x for x in cnt if cnt[x]==3}
    edges=[]
    seen=set()
    for i,c in enumerate(cs):
        if i==guard:
            edges.append(0)
            continue
        sites=[x for x in c if x in spins]
        if len(c)!=3 or len(set(c))!=3 or len(sites)!=2 or sum(cnt[x]==1 for x in c)!=1:
            return dict(status='unsupported')
        e=sum(1<<(x-1) for x in sites)
        if e in seen: return dict(status='unsupported')
        seen.add(e)
        edges.append(e)
    if not seen: return dict(status='unsupported')
    basis=echelon(rows)
    columns=[reduce_word(1<<i,basis) for i in range(q)]
    rank=len(basis)
    used=joins=peak=0
    def pay(cost):
        nonlocal used
        if cost>budget-used: raise Overflow
        used+=cost
    def rec(lo,hi,target):
        nonlocal joins,peak
        pay(1)
        inside=outside=0
        for i,e in enumerate(edges):
            if lo<=i<hi: inside|=e
            else: outside|=e
        border=inside&outside
        comp=echelon(columns[:lo]+columns[hi:])
        def viable(s): return not reduce_word(s^target,comp)
        table={}
        if hi-lo==1:
            e=edges[lo]
            for x in range(1+int(lo!=guard)):
                sy=columns[lo] if x else 0
                if not viable(sy): continue
                z=e
                while True:
                    pay(1)
                    if not x or z!=e:
                        key=sy,z&border
                        table[key]=table.get(key,0)+1
                    if not z: break
                    z=(z-1)&e
        else:
            mid=(lo+hi)//2
            l,bl=rec(lo,mid,target)
            r,br=rec(mid,hi,target)
            pay(len(l)*len(r))
            joins+=len(l)*len(r)
            for (sl,zl),a in l.items():
                for (sr,zr),b in r.items():
                    sy=sl^sr
                    if (zl^zr)&bl&br or not viable(sy): continue
                    key=sy,(zl|zr)&border
                    table[key]=table.get(key,0)+a*b
        peak=max(peak,len(table))
        return table,border
    def coset(w):
        t=reduce_word(w,basis)
        tab,_=rec(0,q,t)
        return tab.get((t,0),0)
    try:
        z=coset(0)
        h=coset(trial) if reduce_word(trial,basis) else z
        exponent=q-1+n-len(cnt)-rank
        if exponent<0:
            score,rem=divmod(z+h,1<<(-exponent))
            if rem: raise ArithmeticError('inexact normalization')
        else: score=(z+h)<<exponent
        count=z<<(exponent+1)
        signed=h<<(exponent+1)
        status='exact'
    except Overflow:
        if fallback is None: return dict(status='budget',work=used,joins=joins,peak=peak)
        count,signed=fallback()
        score,rem=divmod(count+signed,2)
        if rem: raise ArithmeticError('inconsistent fallback')
        status='fallback'
    return dict(status=status,prefix=count,signed=signed,score=score,work=used,joins=joins,peak=peak)
