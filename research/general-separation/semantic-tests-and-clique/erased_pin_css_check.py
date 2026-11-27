"""Bounded erased-pin binary trace checks. Exhaustive functional search is a test oracle."""
from itertools import combinations, permutations, product
from collections import Counter
import networkx as nx
from hidden_cubic_counter import _linear, _apply
from hexacode_pin_strips_check import binary_basis


def span(gen):
    return [_apply(gen,x) for x in range(1<<len(gen))]


def split(w,n):
    return tuple(sum(((w>>(2*i+j))&1)<<i for i in range(n)) for j in range(2))


def join(a,b,n):
    return sum(((a>>i&1)|((b>>i&1)<<1))<<(2*i) for i in range(n))


def erased(A,pins):
    n=len(A);F=[i for i in range(n) if i not in pins]
    data=_linear([(1<<i,1) for i in pins]+[(A[i],0) for i in pins],n)
    if data is None:return None
    origin,delta=data
    def project(x):
        return sum(((x>>i&1)|(((A[i]&x).bit_count()%2)<<1))<<(2*j) for j,i in enumerate(F))
    return F,project(origin),[project(d) for d in delta]


def raw(A,pins):
    P=sum(1<<i for i in pins)
    n=len(A)
    return any(x&P==P and all((x&A[i]).bit_count()%2==0 for i in range(n) if x>>i&1)
               for x in range(1<<n))


def css(F,v,S,transforms):
    n=len(F);full=(1<<n)-1
    def g(w):return sum(transforms[j][w>>(2*j)&3]<<(2*j) for j in range(n))
    u0,v0=split(join(full,full,n)^g(v^join(full,full,n)),n)
    axes=[split(g(w),n) for w in S]
    D=binary_basis(a for a,b in axes)
    E=binary_basis(b for a,b in axes)
    if len(D)+len(E)!=len(S):return None
    B=_linear([(w,0) for w in E],n)[1]
    lookup={w:j for j,w in enumerate(span(B))}
    assert u0 in lookup and all(d in lookup for d in D)
    W=_linear([(lookup[d],0) for d in D],len(B))[1]
    assert len(W)==n-len(S)<=3
    cols=[sum((b>>i&1)<<j for j,b in enumerate(B)) for i in range(n)]
    t=_apply(cols,v0)
    assert t in span(W)
    L=lookup[u0]
    # Bounded trace oracle: extend lambda on W, then ordinary zero-column span test.
    for f in range(1<<len(B)):
        if any(((f^L)&w).bit_count()%2 for w in W):continue
        zero=[i for i,b in enumerate(cols) if not (f&b).bit_count()%2]
        selection=_linear([(sum(((cols[i]>>j)&1)<<z for z,i in enumerate(zero)),(t>>j)&1)
                           for j in range(len(B))],len(zero))
        if selection is None:continue
        second=sum(1<<i for z,i in enumerate(zero) if selection[0]>>z&1)
        first=_apply(B,f)
        assert not first&second
        h=join(first,second,n)
        recovered=sum((3^transforms[i].index(3^((h>>(2*i))&3)))<<(2*i) for i in range(n))
        assert len(binary_basis(S+[recovered^v]))==len(S)
        assert all(((recovered>>(2*i))&3)!=3 for i in range(n))
        return True
    return False


def endo_dimension(A):
    # No trace restriction: test the full sitewise endomorphism algebra.
    n=len(A)
    eq=[]
    for i in range(n):
        for j in range(n):
            row=(1<<(4*i+2)) if i==j else 0
            if A[i]>>j&1:row^=(1<<(4*i+3))^(1<<(4*j))
            for k in range(n):
                if A[i]>>k&A[k]>>j&1:row^=1<<(4*k+1)
            eq.append((row,0))
    return len(_linear(eq,4*n)[1])


if __name__=='__main__':
    maps=[(0,)+t for t in permutations((1,2,3))]
    stats=Counter()
    for G in nx.graph_atlas_g():
        n=len(G)
        if not 3<=n<=5:continue
        A=[sum(1<<j for j in G[i]) for i in range(n)]
        for P in combinations(range(n),3):
            data=erased(A,P)
            truth=raw(A,P)
            if data is None:
                assert not truth
                stats['empty']+=1
                continue
            for g in product(maps,repeat=n-3):
                result=css(*data,g)
                if result is not None:
                    assert result==truth
                    stats['CSS']+=1
                    break
            else:stats['no CSS']+=1
    for m in (2,3):
        edges=[(i,m+j) for i in range(m) for j in range(m)]
        A=[0]*(2*m+m*m)
        for k,(i,j) in enumerate(edges,2*m):
            for v in (i,j):A[k]|=1<<v;A[v]|=1<<k
        A[0]|=2;A[1]|=1
        pins=(0,1,m)
        F,v,S=erased(A,pins)
        g=[(0,1,2,3) if i<2*m else (0,2,1,3) for i in F]
        assert css(F,v,S,g)==raw(A,pins)
        assert endo_dimension(A)==1
    print(stats,'strict scalar-only subdivided K2,2 and K3,3 passed')
