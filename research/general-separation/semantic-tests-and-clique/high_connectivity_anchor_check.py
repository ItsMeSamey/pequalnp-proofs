"""Linear and graph-theoretic controls for both shores of the anchor obstruction."""
from itertools import combinations
from random import Random
import networkx as nx
from hidden_cubic_counter import _linear
from erased_pin_css_check import endo_dimension


def host(t,yes):
    m=5*t+7
    L=list(range(m));R=list(range(m,2*m))
    p,q,r=range(2*m,2*m+3)
    G=nx.Graph()
    for offset in (0,m):
        marks=[offset+5*i for i in range(t)]
        G.add_edges_from(combinations(marks,2))
        for v in marks:nx.add_cycle(G,range(v,v+5))
        nx.add_cycle(G,range(offset+5*t,offset+m))
    G.add_edges_from((i,j) for i in L for j in R)
    h=m+5*t
    G.add_edge(q,r)
    G.add_edges_from((q,i) for i in L)
    G.add_edges_from((r,i) for i in R)
    G.add_edges_from((p,i) for i in L+R if i!=h)
    if yes:G.add_edges_from((r+1,i) for i in [q,r,h]+L)
    A=[sum(1<<j for j in G[i]) for i in range(len(G))]
    return G,A,(p,q,r),m


def mv(A,x):
    return sum(((a&x).bit_count()%2)<<j for j,a in enumerate(A))


def erased_trace(A,pins):
    others=[i for i in range(len(A)) if i not in pins]
    f=len(others)
    ker=_linear([(1<<i,0) for i in pins]+[(A[i],0) for i in pins],len(A))[1]
    gens=[]
    for x in ker:
        y=mv(A,x)
        gens.append(sum((((x>>i)&1)|(((y>>i)&1)<<1))<<(2*j) for j,i in enumerate(others)))
    # Ordinary binary orthogonal vectors provide all linear membership tests.
    dual=_linear([(g,0) for g in gens],2*f)[1]
    eq=[((1<<(4*i))|(1<<(4*i+3)),1) for i in range(f)]
    for g in gens:
        for h in dual:
            coeff=0
            for i in range(f):
                u,v=(g>>(2*i))&1,(g>>(2*i+1))&1
                a,b=(h>>(2*i))&1,(h>>(2*i+1))&1
                coeff|=((a*u)|((a*v)<<1)|((b*u)<<2)|((b*v)<<3))<<(4*i)
            eq.append((coeff,0))
    return _linear(eq,4*f)


def verify(t,yes,rng):
    G,A,pins,m=host(t,yes)
    p,q,r=pins
    P=sum(1<<i for i in pins)
    L=(1<<m)-1
    R=L<<m
    _,ker=_linear([(A[i]&~P,0) for i in pins],len(A))
    assert len(A)-len(ker)==3
    assert endo_dimension(A)==1
    assert erased_trace(A,pins) is None
    connectivity=nx.node_connectivity(G)
    assert connectivity>=m+1 and (yes or connectivity==m+1)
    guesses=[P|(1<<(5*i))|(1<<(m+5*i)) for i in range(t)]
    for i,x in enumerate(guesses):
        y=mv(A,x)
        assert not y&P and x&y
        for j,z in enumerate(guesses):
            if i!=j:assert not z&y
        if yes:assert y>>(r+1)&1
    # Derive the NO certificate from the actual adjacency, valid for all masks.
    assert (A[q]&~P)&(L|R)==L and (A[r]&~P)&(L|R)==R
    assert all((A[i]&R)==R and (A[i]&P).bit_count()==2 for i in range(m))
    assert all((A[i]>>j&1)==(A[j]>>i&1) for i,j in combinations(range(m),2))
    for _ in range(64):
        x=P|rng.getrandbits(2*m)
        y=mv(A,x)
        assert ((y&x&L).bit_count()%2)==((x&L).bit_count()*(x&R).bit_count()%2)
    if yes:
        w=P|(1<<(r+1))
        assert not (w&mv(A,w))
    return connectivity


if __name__=='__main__':
    rng=Random(469)
    for t in range(1,4):
        print('t',t,'NO/YES vertex connectivity',*[verify(t,v,rng) for v in (False,True)])
