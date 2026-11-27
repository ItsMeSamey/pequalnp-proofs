"""One-sided randomized rank search for diag(t)+D(Ht), allowing nonlinear D."""
from functools import reduce
from operator import xor
from random import SystemRandom
from hidden_product_network import encoder
from punctured_witness import BinaryField
from quadratic_centroid import independent
from quadratic_target import apply_basis
from slope_group_algebra import ring_mul


def extension(n):
    d=max(2,(max(1,2*n)-1).bit_length())
    for modulus in range((1<<d)|1,1<<(d+1),2):
        try:
            return BinaryField(modulus)
        except ValueError:
            continue
    raise ArithmeticError("irreducible modulus unavailable")


class GroupRing:
    """Packed bit planes for GF(2^d)[F2^w]; addition is integer XOR."""
    def __init__(self,field,w):
        self.field=field
        self.size=1<<w
        self.mask=(1<<self.size)-1

    def mono(self,a,u):
        return sum(((a>>j)&1)<<(self.size*j+u) for j in range(self.field.m))

    def times(self,a,b):
        if not a or not b:
            return 0
        f=self.field
        planes=[0]*(2*f.m-1)
        for i in range(f.m):
            ai=(a>>(i*self.size))&self.mask
            for j in range(f.m):
                bj=(b>>(j*self.size))&self.mask
                planes[i+j]^=ring_mul(ai,bj)
        for i in reversed(range(f.m,len(planes))):
            for j in range(f.m):
                if (f.modulus>>j)&1:
                    planes[i-f.m+j]^=planes[i]
        return sum(v<<(i*self.size) for i,v in enumerate(planes[:f.m]))

    def coefficient(self,a,u):
        return sum(((a>>(i*self.size+u))&1)<<i for i in range(self.field.m))

    def det(self,matrix):
        def dot(a,b):
            return reduce(xor,(self.times(x,y) for x,y in zip(a,b)),0)
        coeff=[1]
        for k in reversed(range(len(matrix))):
            row=matrix[k][k+1:]
            v=[r[k] for r in matrix[k+1:]]
            col=[1,matrix[k][k]]
            for e in range(len(v)):
                col.append(dot(row,v))
                if e+1<len(v):
                    v=[dot(r[k+1:],v) for r in matrix[k+1:]]
            coeff=[reduce(xor,(self.times(col[j],coeff[i-j]) for j in range(i+1) if i-j<len(coeff)),0)
                   for i in range(len(col))]
        return coeff[-1]


def weighted(ring,actions,D,u,alpha,h,prefix):
    n=len(actions)
    matrix=[[0]*n for _ in range(n)]
    for j,bits in enumerate(D):
        mon=ring.mono(alpha[j],actions[j])
        for i in range(n):
            b=(bits>>i)&1
            zero=b
            one=mon if b^(i==j) else 0
            if j<h:
                matrix[i][j]=one if (prefix>>j)&1 else zero
            else:
                matrix[i][j]=one^zero
    return ring.coefficient(ring.det(matrix),u)


def search(n,forms,frozen,*,syndrome=None,trials=1,rng=None):
    """Return ('FOUND',t) or ('INCONCLUSIVE',None); frozen(u) returns n columns.

    forms are w independent binary row masks of H. Supply a syndrome to
    restrict the search to one H-fiber, or omit it to search all fibers.
    """
    forms=tuple(forms)
    w=len(forms)
    if n<0 or len(independent(forms))!=w or any(not 0<x<1<<n for x in forms) or trials<0:
        raise ValueError("invalid syndrome map or trial count")
    if syndrome is not None and not 0<=syndrome<1<<w:
        raise ValueError("invalid syndrome")
    rng=SystemRandom() if rng is None else rng
    f=extension(n)
    ring=GroupRing(f,w)
    actions=tuple(sum(((h>>j)&1)<<k for k,h in enumerate(forms)) for j in range(n))
    for _ in range(trials):
        alpha=tuple(rng.randrange(f.size) for _ in range(n))
        for u in (range(1<<w) if syndrome is None else (syndrome,)):
            D=tuple(frozen(u))
            if len(D)!=n or any(not 0<=v<1<<n for v in D):
                raise ValueError("invalid frozen matrix")
            if not weighted(ring,actions,D,u,alpha,0,0):
                continue
            t=0
            for j in range(n):
                if not weighted(ring,actions,D,u,alpha,j+1,t):
                    t|=1<<j
            cols=[v^(t&(1<<j)) for j,v in enumerate(D)]
            if apply_basis(actions,t)!=u or len(independent(cols))!=n:
                raise ArithmeticError("rank witness failed replay")
            return 'FOUND',t
    return 'INCONCLUSIVE',None


def witness(n,forms,frozen,target,offset=lambda t:0,**kwargs):
    forms=tuple(forms)
    if not 0<=target<1<<n:
        raise ValueError("invalid target")
    status,t=search(n,forms,frozen,**kwargs)
    if t is None:
        return status,None
    u=sum(((t&h).bit_count()%2)<<j for j,h in enumerate(forms))
    cols=[v^(t&(1<<j)) for j,v in enumerate(frozen(u))]
    base=offset(t)
    y=encoder(cols)(target^base)
    if apply_basis(cols,y)^base!=target:
        raise ArithmeticError("leaf witness failed replay")
    return status,(t,y)


if __name__=='__main__':
    from random import Random
    rng=Random(731)
    n=4
    forms=(3,12)
    actions=(1,1,2,2)
    f=extension(n)
    ring=GroupRing(f,2)
    even=asym=0
    for rep in range(12):
        Ds=[[rng.randrange(16) for j in range(4)] for u in range(4)]
        alpha=[rng.randrange(f.size) for _ in range(4)]
        for u,D in enumerate(Ds):
            good=[t for t in range(16) if apply_basis(actions,t)==u and
                  len(independent([v^(t&(1<<j)) for j,v in enumerate(D)]))==4]
            even+=bool(good) and len(good)%2==0
            asym+=any(((D[i]>>j)^(D[j]>>i))&1 for i in range(n) for j in range(i))
            for h in range(5):
                for prefix in range(1<<h):
                    val=0
                    for t in good:
                        if (t&((1<<h)-1))==prefix:
                            mon=1
                            for j,a in enumerate(alpha):
                                if (t>>j)&1:
                                    mon=f.mul(mon,a)
                            val^=mon
                    assert weighted(ring,actions,D,u,alpha,h,prefix)==val
            status,t=search(4,forms,Ds.__getitem__,syndrome=u,trials=12,rng=rng)
            assert (status=='FOUND')==bool(good)
            if t is not None:
                assert t in good
        status,result=witness(4,forms,Ds.__getitem__,3,lambda t:t,trials=12,rng=rng)
        if result:
            t,y=result
            D=Ds[apply_basis(actions,t)]
            assert apply_basis([v^(t&(1<<j)) for j,v in enumerate(D)],y)^t==3
    assert even and asym
    print('1488 weighted prefix comparisons;',even,'nonempty even fibers;',asym,'asymmetric fibers')
