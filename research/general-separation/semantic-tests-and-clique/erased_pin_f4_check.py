"""Finite verification of erased GF4 fibers, Hermitian purification, and zero fusion."""
from itertools import combinations,product
from collections import Counter
import networkx as nx
from erased_pin_css_check import erased,raw,span,split
from hexacode_pin_strips_check import binary_basis
from hermitian_three_pin_check import coord,mul,scale,ratio,solve,even_witness
from hidden_cubic_counter import _linear,_apply


def herm(x,y,n):
    h=0
    for j in range(n):
        a=coord(y,j)
        h^=mul(coord(x,j),mul(a,a))
    return h


def zero_pair(gen,n):
    # Two named zeros are first. Require remaining sites nonzero, and optionally
    # rescale at the third site after solving.
    def syndrome(w):return coord(w,0)^coord(w,1)
    ker=_linear([(sum(((syndrome(w)>>i)&1)<<j for j,w in enumerate(gen)),0)
                 for i in (0,1)],len(gen))[1]
    fused=[_apply(gen,x) for x in ker]
    piv={}
    pure=False
    for w in fused:
        while w>>4 and w.bit_length() in piv:w^=piv[w.bit_length()]
        if w>>4:piv[w.bit_length()]=w
        elif w:pure=True
    rows=list(piv.values())
    f=n-2
    assert len(rows)==f
    xcols,ycols=[[sum(((w>>(4+2*i+b))&1)<<j for j,w in enumerate(rows))
                  for i in range(f)] for b in (0,1)]
    # Choose one member at every site that gives independent x columns. Small
    # chart search here is bounded; the polynomial swaps are in the fusion solver.
    for mask in range(1<<f):
        cols=[ycols[i] if mask>>i&1 else xcols[i] for i in range(f)]
        if len(binary_basis(cols))==f:break
    else:raise AssertionError('missing chart')
    ys=[xcols[i] if mask>>i&1 else ycols[i] for i in range(f)]
    A=[]; lifts=[]
    for i in range(f):
        w=_linear([(col,int(i==j)) for j,col in enumerate(cols)],f)[0]
        lifts.append(_apply(rows,w))
        a=sum(((w&v).bit_count()%2)<<j for j,v in enumerate(ys))
        A.append(a&~(1<<i))
    assert all(a.bit_count()%2 for a in A)
    colors=[coord(w,0) for w in lifts] if not pure else [0]*f
    target=0
    for d in colors:target^=d
    z=even_witness(A,colors,target)
    if z is None:return None
    out=_apply(lifts,((1<<f)-1)^z)
    if pure:out&=~15
    assert out&15==0 and all(coord(out,j) for j in range(2,n))
    return out


def named(gen,n,targets):
    s=len(targets)
    # Aux sites first. If none/one/two are named, pad with arbitrary nonzero
    # pin values on remaining physical sites (at most 27 constant trials).
    zero=[j for j,t in enumerate(targets) if not t]
    assert len(zero)%2==0
    if zero:
        perm=zero+[i for i in range(n) if i not in zero]
        def reorder(w,ids):return sum(coord(w,i)<<(2*j) for j,i in enumerate(ids))
        w=zero_pair([reorder(v,perm) for v in gen],n)
        if w is None:return None
        w=reorder(w,[perm.index(i) for i in range(n)])
        for i,t in enumerate(targets):
            if t:w=scale(w,ratio(t,coord(w,i)),n);break
        return w
    if n<3:
        return next((w for w in span(gen) if all(coord(w,i) for i in range(n))
                     and all(coord(w,i)==t for i,t in enumerate(targets))),None)
    for extra in product((1,2,3),repeat=3-s):
        w,_=solve(n,gen,tuple(targets)+extra)
        if w is not None:return w
    return None


def test_case(F,v,S):
    n=len(F)
    full=(1<<(2*n))-1
    for mask in range(1<<n):
        def g(w):
            out=w
            for i in range(n):
                if mask>>i&1 and coord(w,i) in (1,2):out^=3<<(2*i)
            return out
        C=[g(w) for w in S]
        if len(binary_basis(C+[scale(w,2,n) for w in C]))==len(C):break
    else:return None
    d=n-len(C)
    assert 0<=d<=3
    c0=g(v)^full
    kernel=_linear([(sum(((herm(1<<j,b,n)>>i)&1)<<j for j in range(2*n)),0)
                     for i in (0,1) for b in C],2*n)[1]
    assert all(herm(c0,b,n)==0 for b in C)
    quotient=[]
    # Gram-Schmidt in the at-most-three-dimensional quotient. The finite
    # checker enumerates its small ambient perpendicular to pick representatives.
    perp=span(kernel)
    for _ in range(d):
        e=next(w for w in perp if herm(w,w,n)==1 and all(herm(w,u,n)==0 for u in quotient))
        quotient.append(e)
    def phi(w):return sum(herm(w,e,n)<<(2*i) for i,e in enumerate(quotient))
    gen=[(w<<(2*d))|phi(w) for w in kernel]
    targets=[coord(phi(c0),i) for i in range(d)]
    assert len(gen)*2==2*(n+d) and all(herm(a,b,n+d)==0 for a in gen for b in gen)
    w=named(gen,n+d,targets)
    if w is not None:
        assert w in span(gen)
        assert all(coord(w,i)==t for i,t in enumerate(targets))
        assert all(coord(w,i) for i in range(d,n+d))
        recovered=g((w>>(2*d))^full)
        assert recovered^v in span(S) and all(coord(recovered,i)!=3 for i in range(n))
    return w is not None,targets.count(0)


if __name__=='__main__':
    stats=Counter()
    for G in nx.graph_atlas_g():
        n=len(G)
        if not 3<=n<=6:continue
        A=[sum(1<<j for j in G[i]) for i in range(n)]
        for P in combinations(range(n),3):
            data=erased(A,P)
            if data is None:continue
            sol=test_case(*data)
            if sol is not None:
                ok,zeros=sol
                assert ok==raw(A,P)
                stats[zeros]+=1
    assert stats[2]>0
    print('purified cases by zero pin count',dict(stats))
