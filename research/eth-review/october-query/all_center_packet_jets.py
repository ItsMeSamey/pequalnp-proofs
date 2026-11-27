"""Truncated Hasse jets in a new Z direction; original U,V arithmetic stays in base Ring."""
from itertools import combinations,product
from math import comb
from collections import Counter
from partial_shift_affine import character_sum
from variable_packet_machine import shifted_kernel
from packet_entry_tape import Ring,canonical_lift
from tapered_jet_machine import valuation

class JetRing:
    """Z-major coefficients, each internally in source U-fast order."""
    def __init__(self,base,J):
        self.base,self.p,self.J=base,base.p,J
        self.width=len(base.f)*base.ell
        self.cost=Counter()
    def scalar(self,n):
        self.cost['jet_scalars']+=1
        return self.base.scalar(n)+(0,)*(self.width*(self.J-1))
    def add(self,a,b):
        self.cost['jet_adds']+=1
        return tuple((u+v)% (1<<self.p) for u,v in zip(a,b))
    def mul(self,a,b):
        self.cost['jet_muls']+=1
        d=self.width
        out=[]
        for k in range(self.J):
            v=self.base.scalar(0)
            for i in range(k+1):
                x=a[d*i:d*(i+1)]
                y=b[d*(k-i):d*(k-i+1)]
                if any(x) and any(y):
                    self.cost['base_muls']+=1
                    v=self.base.add(v,self.base.mul(x,y))
            out.extend(v)
        return tuple(out)

def evaluate(edges,packets,base,zeta,*,center,J,parity=None,sign=0,term_cap=None):
    """Return J coefficients of F(center+2L*(zeta+Z)) modulo 2^base.p, or None at cap.
    zeta is a base-ring residue at the requested working precision.
    """
    if J<1 or base.p<1 or base.ell<1 or not base.f or term_cap is not None and term_cap<0:
        raise ValueError('invalid jet parameters')
    if len(zeta)!=len(base.f)*base.ell: raise ValueError('bad evaluation point')
    ring=JetRing(base,J)
    point=tuple(x%(1<<base.p) for x in zeta)+(base.scalar(1) if J>1 else ())+(0,)*(ring.width*max(0,J-2))
    edges = tuple(tuple(e) for e in edges)
    packets = tuple(tuple(pk) for pk in packets)
    e = len(edges)
    if not e or not packets or any(len(edge)!=2 or edge[0]==edge[1] for edge in edges):
        raise ValueError("expected nonempty loopless edge list")
    L = len(packets[0])
    if L < 2 or L & (L-1) or any(len(pk)!=L for pk in packets):
        raise ValueError("expected uniform power-of-two packet lengths")
    ports = [i for pk in packets for i in pk if i is not None]
    if any(type(i) is not int for i in ports) or sorted(ports)!=list(range(2*e)):
        raise ValueError("physical ports must occur exactly once")
    if not 0 <= sign < 1 << (3*e) or ring.p<1:
        raise ValueError("invalid sign or precision")
    vertices = {}
    for j,edge in enumerate(edges):
        for b,v in enumerate(edge):
            vertices[v]=vertices.get(v,0) | (1<<(2*j+b))
    parity = {} if parity is None else parity
    if set(parity)-vertices.keys() or any(b not in (0,1) for b in parity.values()):
        raise ValueError("invalid vertex parity")
    old=[(row,parity.get(v,0)) for v,row in vertices.items()]
    kmax=min(2*e,ring.p-(e-len(vertices))-1)
    if not -L<=center<L: raise ValueError('center outside source grid')
    limit=sum(comb(2*e,k)*L**k for k in range(kmax+1))
    if term_cap is not None and limit>term_cap: return None
    zero=ring.scalar(0)
    stats={'orders':0,'row_sets':0,'terms':0,'nonzero_terms':0,'kernel_entries':0}
    if kmax<0:
        return tuple(base.scalar(0) for _ in range(J)),dict(stats,precision=base.p,J=J,term_bound=limit)
    kernel={d:shifted_kernel(ring,L,center,point,d) for d in range(1-L,L)}
    stats['kernel_entries']=len(kernel)
    ties=[None]*(2*e)
    correction=[None]*(2*e)
    for pk in packets:
        for i,row in enumerate(pk):
            if row is None:
                continue
            successor=pk[i+center] if 0<=i+center<L else None
            mask=0 if successor is None else 1<<(2*e+successor//2)
            ties[row]=((1<<row)|mask,0)
            by_edge={}
            for j,col in enumerate(pk):
                if col is None:
                    continue
                coef=kernel[j-i]
                if j==i+center:
                    coef=ring.add(coef,ring.scalar(-1))
                if any(x&1 for x in coef):
                    raise ArithmeticError("native kernel disagrees with mod-two partial shift")
                x=col//2
                by_edge[x]=ring.add(by_edge.get(x,zero),coef)
            correction[row]=[(x,c) for x,c in by_edge.items() if c!=zero]
    total=zero
    for k in range(kmax+1):
        stats['orders']+=1
        for defects in combinations(range(2*e),k):
            stats['row_sets']+=1
            defect_mask=sum(1<<i for i in defects)
            equalities=old+[t for i,t in enumerate(ties) if not (defect_mask>>i)&1]
            for choices in product(*(correction[i] for i in defects)):
                stats['terms']+=1
                pins=[(1<<(2*e+x),1) for x,_ in choices]
                mass=character_sum(3*e,equalities+pins,sign^defect_mask)
                coef=ring.scalar(-mass if k%2 else mass)
                for _,w in choices:
                    coef=ring.mul(coef,w)
                if coef!=zero:
                    stats['nonzero_terms']+=1
                    total=ring.add(total,coef)
    return tuple(total[i*ring.width:(i+1)*ring.width] for i in range(J)),dict(stats,**ring.cost,precision=base.p,J=J,term_bound=limit)

def native(edges,packets,f,ell,p,u,t,*,parity=None,sign=0,term_cap=None):
    """Source active jet centered at zeta=0; executes at its actual increased precision."""
    m=2*len(edges)
    L=len(packets[0])
    a=L.bit_length()-1
    if not (1<=u<=min(a,m) and p>=1 and -L<=t<L and t!=0 and valuation(t)<u):
        raise ValueError('not an active native center')
    i=valuation(t)
    h=(3*m+u-1)//u
    pt=p+8*h*(L>>i)+8*m*(a+1)
    rr=Ring(pt,tuple(f),ell)
    return evaluate(edges,packets,rr,rr.scalar(0),center=t,J=h*(u-i),
                    parity=parity,sign=sign,term_cap=term_cap)
