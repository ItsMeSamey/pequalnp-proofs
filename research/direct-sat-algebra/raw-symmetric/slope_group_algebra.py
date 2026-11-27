"""Prefix parity for binary pencils with low-rank off-diagonal variation."""
from dataclasses import dataclass
from functools import reduce
from operator import xor
from hidden_product_network import encoder
from quadratic_centroid import independent
from quadratic_target import apply_basis


def fwht(a):
    h=1
    while h<len(a):
        for j in range(0,len(a),2*h):
            for k in range(j,j+h):
                s,t=a[k],a[k+h]
                a[k],a[k+h]=s+t,s-t
        h*=2


def ring_mul(a,b):
    if not a or not b:
        return 0
    if a==1 or b==1:
        return b if a==1 else a
    size=1<<(max(a,b).bit_length()-1).bit_length()
    def unpack(x):
        buf=x.to_bytes((size+7)//8,'little')
        return [(buf[i//8]>>(i%8))&1 for i in range(size)]
    u=unpack(a)
    v=unpack(b)
    fwht(u)
    fwht(v)
    z=[s*t for s,t in zip(u,v)]
    fwht(z)
    out=bytearray((size+7)//8)
    for i,s in enumerate(z):
        out[i//8]|=((s//size)&1)<<(i%8)
    return int.from_bytes(out,'little')


def dot(a,b):
    return reduce(xor,(ring_mul(x,y) for x,y in zip(a,b)),0)


def ring_det(matrix):
    """Division-free Berkowitz characteristic-polynomial recurrence."""
    coeff=[1]
    for k in reversed(range(len(matrix))):
        row=matrix[k][k+1:]
        v=[r[k] for r in matrix[k+1:]]
        col=[1,matrix[k][k]]
        for e in range(len(v)):
            col.append(dot(row,v))
            if e+1<len(v):
                v=[dot(r[k+1:],v) for r in matrix[k+1:]]
        coeff=[reduce(xor,(ring_mul(col[j],coeff[i-j]) for j in range(i+1) if i-j<len(coeff)),0)
               for i in range(len(col))]
    return coeff[-1]


@dataclass
class Pencil:
    """entries[(row,col)] = (constant bit, raw control mask) for row!=col."""
    n:int
    entries:dict
    diagonal_offset:int=0

    def __post_init__(self):
        n=self.n
        if n<0 or not 0<=self.diagonal_offset<1<<n:
            raise ValueError("invalid diagonal offset")
        for (i,j),(c,mask) in self.entries.items():
            if not (0<=i<n and 0<=j<n and i!=j and c in (0,1) and 0<=mask<1<<n):
                raise ValueError("invalid off-diagonal")
        self.forms=independent(mask for c,mask in self.entries.values())
        self.w=len(self.forms)
        encode=encoder(self.forms)
        self.actions=tuple(sum(((h>>j)&1)<<k for k,h in enumerate(self.forms)) for j in range(n))
        self.reduced={ij:(c,encode(mask)) for ij,(c,mask) in self.entries.items()}

    def frozen_columns(self,u):
        cols=[self.diagonal_offset&(1<<i) for i in range(self.n)]
        for (i,j),(c,mask) in self.reduced.items():
            cols[j]|=(c^((u&mask).bit_count()%2))<<i
        return cols

    def columns(self,t):
        u=apply_basis(self.actions,t)
        return [c^(t&(1<<j)) for j,c in enumerate(self.frozen_columns(u))]

    def parity(self,h,prefix):
        if not 0<=h<=self.n or not 0<=prefix<1<<h:
            raise ValueError("invalid prefix")
        total=0
        for u in range(1<<self.w):
            mat=[[0]*self.n for _ in range(self.n)]
            for j,c in enumerate(self.frozen_columns(u)):
                z=1<<self.actions[j]
                for i in range(self.n):
                    b=(c>>i)&1
                    if j<h:
                        t=(prefix>>j)&1
                        mat[i][j]=(z if t else 1) if b^(t and i==j) else 0
                    else:
                        mat[i][j]=((1^z) if b else 0)^(z if i==j else 0)
            total^=(ring_det(mat)>>u)&1
        return total

    def witness(self,target,offset=lambda t:0):
        if not 0<=target<1<<self.n:
            raise ValueError("invalid target")
        if not self.parity(0,0):
            return None
        t=0
        for j in range(self.n):
            if not self.parity(j+1,t):
                t|=1<<j
        cols=self.columns(t)
        add=offset(t)
        y=encoder(cols)(target^add)
        if apply_basis(cols,y)^add!=target:
            raise ArithmeticError("target replay failed")
        return t,y


def section_witness(section,target):
    """Use a supplied normalized raw binary section, accepting asymmetric fixed drift."""
    n=len(section.leaves)
    if len(section.centers)!=n:
        return None
    raw=section.raw
    base=raw(0)
    fixed=[raw(y)^base for y in section.leaves]
    if any(raw(y^z)^raw(y)^raw(z)^base for i,y in enumerate(section.leaves) for z in section.leaves[:i]):
        return None
    masks=[[0]*n for _ in range(n)]
    for k,x in enumerate(section.centers):
        for j,y in enumerate(section.leaves):
            v=raw(x^y)^raw(x)^raw(y)^base
            for i in range(n):
                masks[i][j]|=((v>>i)&1)<<k
    if any(masks[i][i]!=1<<i for i in range(n)):
        return None
    entries={(i,j):((fixed[j]>>i)&1,masks[i][j]) for j in range(n) for i in range(n) if i!=j}
    pencil=Pencil(n,entries,sum(fixed[i]&(1<<i) for i in range(n)))
    ans=pencil.witness(target,lambda t:raw(apply_basis(section.centers,t)))
    if ans is None:
        return None
    t,y=ans
    result=apply_basis(section.centers,t)^apply_basis(section.leaves,y)
    if raw(result)!=target:
        raise ArithmeticError("raw section replay failed")
    return result


if __name__=='__main__':
    from itertools import product
    from random import Random
    rng=Random(9472)
    cases=0
    for n in range(1,5):
        for wanted in sorted({0,1,n}):
            for sym in (False,True):
                entries={}
                for i,j in product(range(n),repeat=2):
                    if i!=j:
                        mask=entries[j,i][1] if sym and j<i else rng.randrange(1<<wanted)
                        entries[i,j]=(rng.randrange(2),mask)
                if n>=3 and wanted==n:
                    for i in range(n):
                        j=(i+1)%n
                        entries[i,j]=(0,1<<i)
                        if sym:
                            entries[j,i]=(1,1<<i)
                p=Pencil(n,entries,rng.randrange(1<<n))
                if n>=3 and wanted==n:
                    assert p.w==n
                good=[int(len(independent(p.columns(t)))==n) for t in range(1<<n)]
                for h in range(n+1):
                    for x in range(1<<h):
                        assert p.parity(h,x)==sum(good[x::1<<h])%2
                        cases+=1
                if sym:
                    assert sum(good)%2
                ans=p.witness(1,lambda t:t)
                assert (ans is None)==(sum(good)%2==0)
                if ans:
                    t,y=ans
                    assert apply_basis(p.columns(t),y)^t==1
    from raw_symmetric_section import Section
    p=Pencil(3,{(0,2):(1,3),(2,0):(0,3)},6)
    def raw(x):
        return apply_basis(p.columns(x&7),x>>3)^(x&7)
    chart=Section((8,16,32),(1,2,4),raw,0)
    assert all(raw(section_witness(chart,target))==target for target in range(8))
    print(cases,'prefix comparisons, extreme w, and 8 asymmetric raw targets passed')
