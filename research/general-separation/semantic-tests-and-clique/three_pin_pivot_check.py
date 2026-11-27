"""Check labeled edge pivots, Schur residuals and reverse witness lifting."""
from collections import Counter
from itertools import combinations
import networkx as nx


def bits(mask):
    while mask:
        one=mask&-mask
        yield one.bit_length()-1
        mask^=one


def matvec(A,x):
    return sum(((row&x).bit_count()%2)<<i for i,row in enumerate(A))


def rank(rows):
    basis={}
    for v in rows:
        while v:
            i=v.bit_length()
            if i not in basis:
                basis[i]=v
                break
            v^=basis[i]
    return len(basis)


def edge_pivot(A,i,j):
    assert A[i]>>j&1
    pair=(1<<i)|(1<<j)
    n=len(A)
    # Solve y=Ax with swapped coordinates at i,j, one new input column at a time.
    columns=[]
    for col in range(n):
        new=1<<col
        x=new&~pair
        rhs=new^matvec(A,x)
        x|=((rhs>>i&1)<<j)|((rhs>>j&1)<<i)
        columns.append((matvec(A,x)&~pair)|(x&pair))
    assert all(not(v>>i&1) for i,v in enumerate(columns))
    assert all((columns[i]>>j&1)==(columns[j]>>i&1) for j in range(n) for i in range(j))
    return columns


def verify(A,S,P):
    n=len(A)
    history=[]
    swapped=0
    current=A
    def delete(D):
        nonlocal current
        if D:
            history.append((current,0,D))
            current=[row&~D if not (D>>i&1) else 0 for i,row in enumerate(current)]
    def eliminate(D):
        nonlocal current,swapped
        left=D
        while any(row&left for i,row in enumerate(current) if left>>i&1):
            i=next(i for i in bits(left) if current[i]&left)
            j=next(bits(current[i]&left))
            pair=(1<<i)|(1<<j)
            history.append((current,pair,0))
            current=edge_pivot(current,i,j)
            swapped^=pair
            left^=pair
        return left

    delete(((1<<n)-1)^S)
    free=S^P
    d=free.bit_count()-rank(current[i]&free for i in bits(free))
    D=eliminate(free)
    assert d==D.bit_count()<=P.bit_count()-1
    delete(free^D)
    N=[current[i]&P for i in bits(D)]
    assert all(not(current[i]&D) for i in bits(D))
    assert rank(N)==d and all(r.bit_count()%2==0 for r in N)
    B=next(sum(1<<j for j in subset) for subset in combinations(bits(P),d)
           if rank(row&sum(1<<j for j in subset) for row in N)==d)
    assert eliminate(B|D)==0
    delete(D)
    assert (swapped&P)==B
    x=P^B
    assert matvec(current,x)==B
    for original,pair,removed in reversed(history):
        y=matvec(current,x)
        if pair:
            old_x=(x&~pair)|(y&pair)
            assert matvec(original,old_x)==((y&~pair)|(x&pair))
            x=old_x
        else:
            assert not (x&removed)
        current=original
        assert not(x&matvec(current,x))
    assert x==S and not (x&matvec(A,x)) and x&P==P
    return d


if __name__=='__main__':
    bins=Counter()
    for graph in nx.graph_atlas_g():
        n=len(graph)
        if not 3<=n<=6:continue
        A=[sum(1<<j for j in graph[i]) for i in range(n)]
        valid=[x for x in range(1<<n) if not(x&matvec(A,x))]
        for triple in combinations(range(n),3):
            P=sum(1<<j for j in triple)
            candidates=[x for x in valid if x&P==P]
            for S in candidates:
                if not any(T!=S and T&S==T for T in candidates):
                    bins[verify(A,S,P)]+=1
    assert set(bins)=={0,1,2}
    path=[2,5,2]
    assert 7&matvec(path,7)
    assert matvec(path,2)==5
    print('minimal supports by residual nullity',dict(sorted(bins.items())),'wrong leaf orientations detected')
