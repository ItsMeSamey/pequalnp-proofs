"""Independent truth-table and source-fiber checks of degree-bounded policies."""
import random
from itertools import product
from controlled_policy_peeling import exact, policy_constants


def span(values):
    out={0}
    for v in values:
        out.update([x^v for x in out])
    return out


def active(q,y):
    return (q[0]&y).bit_count()%2 ^ q[1]


def verify(m,A,b,U,Q,d):
    n=len(A)
    tables={}
    def reduce(v):
        while v and (v&-v) in tables:
            v ^= tables[v&-v]
        return v
    for u,q in zip(U,Q):
        for s in range(1<<n):
            if s.bit_count()>d:
                continue
            v=reduce(sum(u<<(m*y) for y in range(1<<n) if active(q,y) and y&s==s))
            if v:
                tables[v&-v]=v
    expected={u for u in range(1<<m) if not reduce(sum(u<<(m*y) for y in range(1<<n)))}
    W=policy_constants(m,n,U,Q,d)
    assert expected==span(v for v,_ in W.values())
    valid=set()
    for y in range(1<<n):
        rhs=b
        for i,v in enumerate(A):
            if y>>i&1:
                rhs ^= v
        for x in range(1<<len(U)):
            lhs=0
            for i,(u,q) in enumerate(zip(U,Q)):
                if x>>i&1 and active(q,y):
                    lhs ^= u
            if lhs==rhs:
                valid.add((x,y))
    for terminal in ('brute','character'):
        cnt,w,_=exact(m,A,b,U,Q,d,terminal=terminal)
        assert cnt==len(valid) and (w in valid if cnt else w is None)
    return expected


def patterns(n):
    U,Q=[],[]
    for j in range(1<<n):
        dirs=[1<<(1+j*(n-1)+i) for i in range(n-1)]
        U.extend(dirs+[1+sum(dirs)])
        Q.extend((1<<i,1^(j>>i&1)) for i in range(n))
    return U,Q


if __name__=='__main__':
    rng=random.Random(4819)
    for A,b,u1,u2,f1,f2 in product(range(2),range(2),range(2),range(2),range(4),range(4)):
        for d in (0,1):
            verify(1,[A],b,[u1,u2],[(f1>>1,f1&1),(f2>>1,f2&1)],d)
    for _ in range(240):
        n,k,m=(rng.randrange(5) for _ in range(3))
        A=[rng.randrange(1<<m) for _ in range(n)]
        U=[rng.randrange(1<<m) for _ in range(k)]
        Q=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(k)]
        verify(m,A,rng.randrange(1<<m),U,Q,rng.randrange(n+2))
    U=[2,1,3,1]
    Q=[(2,0),(2,1),(3,0),(3,1)]
    assert verify(2,[1,2],1,U,Q,0)=={0}
    assert verify(2,[1,2],1,U,Q,1)=={0,1}
    U2=U+[1,2,3,2]
    Q2=Q+[(v<<2,c) for v,c in Q]
    assert verify(2,[1,2,3,1],2,U2,Q2,1)==set(range(4))
    for n in (2,3):
        U,Q=patterns(n)
        m=1+(n-1)*(1<<n)
        assert not policy_constants(m,n,U,Q,n-2)
        assert span(v for v,_ in policy_constants(m,n,U,Q,n-1).values())=={0,1}
        N,w,s=exact(m,[0]*n,0,U,Q,n-1,terminal='brute')
        assert N=={2:64,3:32768}[n] and w is not None and s['signed_exponent']==-1
        print(n,'variables, source count',N,'residual count',2*N,'rounds',s['rounds'])
    print('512 exhaustive degree checks, 240 randomized pencils, strict policies and two negative exponents passed')
