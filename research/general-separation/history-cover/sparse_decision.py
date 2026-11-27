"""Guarded sparse backward SAT compiler for ordered original circuits."""
from cover import direct


class Limit(Exception):
    """Budget exhaustion gives an inconclusive result."""


def specialize(poly, bit, value):
    ans=set()
    for term in poly:
        if not term & bit or value:
            ans.symmetric_difference_update([term & ~bit])
    return ans


def solve(n,gates,out,term_cap,work_cap,pins=0,values=0,peel=True):
    if min(n,pins,values,term_cap,work_cap)<0 or pins>>n or values&~pins:
        raise ValueError('invalid bounds or pins')
    for i,g in enumerate(gates):
        if len(g)!=3 or any(f<0 or f>>(n+1+i) for f in g):
            raise ValueError('unordered circuit')
    if out<0 or out>>(n+1+len(gates)):
        raise ValueError('invalid output')
    used=0
    def charge(k):
        nonlocal used
        used+=k
        if used>work_cap:
            raise Limit('work cap')
    def add(s,t):
        charge(1)
        s.symmetric_difference_update([t])
        if len(s)>term_cap:
            raise Limit('term cap')
    def affine(mask):
        v=mask>>1
        constant=(mask&1)^((v&values).bit_count()&1)
        v&=~pins
        terms={0} if constant else set()
        while v:
            b=v&-v
            add(terms,b)
            v^=b
        if len(terms)>term_cap:
            raise Limit('term cap')
        return terms
    def strip(p):
        nonlocal pins,values
        if not peel or not p:
            return p
        raw=0
        for term in p:
            raw |= term
        raw &= ((1<<n)-1)&~pins
        while raw and p:
            b=raw&-raw
            raw^=b
            charge(2*len(p))
            lo,hi=specialize(p,b,0),specialize(p,b,1)
            if not lo or not hi:
                pins|=b
                if not lo:
                    values|=b
                    p=hi
                else:
                    p=lo
        return p
    poly=strip(affine(out))
    for i in reversed(range(len(gates))):
        b=1<<(n+i)
        charge(len(poly))
        if not any(t&b for t in poly):
            continue
        u,v,w=gates[i]
        rhs=affine(w)
        a,c=affine(u),affine(v)
        for x in a:
            for y in c:
                add(rhs,x|y)
        result=set()
        for t in poly:
            if not t&b:
                add(result,t)
            else:
                for h in rhs:
                    add(result,(t^b)|h)
        poly=strip(result)
    if not poly:
        return None,used
    # An inclusion-minimal support in a squarefree ANF is itself a witness.
    witness=min(poly,key=int.bit_count)|values
    assert witness & pins == values and direct(n,gates,out,witness)
    return witness,used
