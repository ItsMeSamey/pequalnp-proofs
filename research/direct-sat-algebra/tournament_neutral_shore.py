"""Compile an ordered unit-loop transitive shore into residual outside systems."""
from quadratic_target import apply_basis,insert,reduce_vector,parity


def compile_shore(M,U,L=(),pins=()):
    n=len(M)
    U=tuple(U)
    if any(not 0<=r<1<<n for r in (*M,*L)) or len(set(U))!=len(U) or any(not 0<=i<n for i in U):
        raise ValueError("invalid rows or shore")
    V=tuple(i for i in range(n) if i not in set(U))
    if not set(pins)<=set(V):
        raise ValueError("named coordinates must lie outside the shore")
    if any(((M[i]>>j)&1)==((M[j]>>i)&1) for i in range(n) for j in range(i)):
        raise ValueError("expected complementary tournament arcs")
    if any((M[i]>>j)&1!=int(a<=b) for a,i in enumerate(U) for b,j in enumerate(U)):
        raise ValueError("shore must be ordered upper triangular with unit loops")
    def restrict(r,indices):
        return sum(((r>>i)&1)<<a for a,i in enumerate(indices))
    B=[restrict(M[i],V) for i in U]
    R=[]
    echelon={}
    labels=[]
    for i,b in zip(U,B):
        if insert(b,1<<len(R),echelon):
            R.append(b)
        labels.append((reduce_vector(b,echelon)[1],sum(((r>>i)&1)<<a for a,r in enumerate(L))))
    k=len(R)
    def finalize(acc,last,nxt):
        if last is None:
            return acc
        v,l=last
        left=1|(v<<1)|(l<<(k+1))
        diff=v^nxt
        return acc^sum(diff<<(k*j) for j in range(left.bit_length()) if left>>j&1)
    states={(0,None):0}
    for i,last in enumerate(labels):
        next_states=states.copy()
        for (acc,prev),path in states.items():
            next_states.setdefault((finalize(acc,prev,last[0]),last),path|(1<<i))
        states=next_states
    residuals={}
    mask=(1<<k)-1
    for (acc,last),path in states.items():
        packed=finalize(acc,last,0)
        cor=[apply_basis(R,(packed>>(k*j))&mask) for j in range(k+1+len(L))]
        D=tuple(restrict(M[i],V)^cor[0]^apply_basis(cor[1:k+1],
                sum(((r>>a)&1)<<j for j,r in enumerate(R))) for a,i in enumerate(V))
        read=tuple(restrict(r,V)^c for r,c in zip(L,cor[k+1:]))
        residuals.setdefault((D,read),path)
    return V,restrict(sum(1<<i for i in set(pins)),V),residuals


def lift(M,U,V,path,y):
    z=sum(((y>>j)&1)<<i for j,i in enumerate(V))
    last=0
    for j in reversed(range(len(U))):
        if path>>j&1:
            i=U[j]
            now=parity(M[i]&sum(((y>>a)&1)<<v for a,v in enumerate(V)))
            z|=(last^now)<<i
            last=now
    return z
