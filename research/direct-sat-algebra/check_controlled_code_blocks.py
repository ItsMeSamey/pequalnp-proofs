"""Compare the separator algorithms with independent original-pencil oracles."""
from itertools import product
from random import Random
from controlled_code_blocks import balanced, solve


def apply(cols,bits):
    v=0
    for i,col in enumerate(cols):
        if bits>>i&1:
            v^=col
    return v


def legal(A,b,U,forms,x,y):
    q=sum((((f&y).bit_count()%2)^c)<<i for i,(f,c) in enumerate(forms))
    return apply(A,y)^b==apply(U,x&q)


def check_case(m,A,b,U,q,tree):
    n,k=len(A),len(U)
    expected=sum(legal(A,b,U,q,x,y) for x in range(1<<k) for y in range(1<<n))
    for mode in ("split","terminal","auto"):
        for decision in (False,True):
            value,witness,_=solve(m,A,b,U,q,tree,policy=mode,decision_only=decision)
            assert value==(bool(expected) if decision else expected)
            if witness is not None:
                assert legal(A,b,U,q,*witness)
            assert (witness is not None)==bool(expected)


def triangle(length):
    edges=[e for i in range(length) for e in
           ((2*i,2*i+1),(2*i+1,2*i+2),(2*i,2*i+2))]
    m=len(edges)
    A=[sum(1<<i for i,(u,v) in enumerate(edges) if u==j) for j in range(2*length+1)]
    U=[1<<i for i in range(m)]
    forms=[((1<<u)|(1<<v),0) for u,v in edges]
    tree=balanced([balanced(range(3*i,3*i+3)) for i in range(length)])
    return m,A,0,U,forms,tree


def triangle_reference(length):
    # Keep the value of the contact vertex already chosen on the left.
    counts=[1,1]
    for _ in range(length):
        nxt=[0,0]
        for left,mid,right in product((0,1),repeat=3):
            if left+mid+right<=1:
                nxt[right]+=counts[left]*(8 if left+mid+right==0 else 2)
        counts=nxt
    return sum(counts)


def main():
    cases=0
    for a,b,d,e,v,c,t,s in product((0,1),repeat=8):
        check_case(1,[a],b,[d,e],[(v,c),(t,s)],(0,1))
        cases+=1
    rng=Random(379101)
    for _ in range(200):
        m,n,k=[rng.randrange(6) for _ in range(3)]
        A=[rng.randrange(1<<m) for _ in range(n)]
        U=[rng.randrange(1<<m) for _ in range(k)]
        q=[(rng.randrange(1<<n),rng.randrange(2)) for _ in U]
        tree=balanced(rng.sample(range(k),k))
        check_case(m,A,rng.randrange(1<<m),U,q,tree)
        cases+=1
    for length in (1,2,3,5,12,24):
        args=triangle(length)
        value,witness,stats=solve(*args)
        expected=triangle_reference(length)
        assert value==expected and value%(1<<length)==0
        assert legal(*args[1:5],*witness) and stats["max_width"]<=3
        if length<=2:
            check_case(*args)
        print("triangles",length,"count",value,"width",stats["max_width"],"clock",stats["clock"])
    # Dense syndrome columns for q and only one independent w column.
    k=18
    A=[(1<<i)^((1<<k)-1) for i in range(k)]
    U=[1]*k
    q=[(1<<i,0) for i in range(k)]
    value,witness,stats=solve(k,A,0,U,q)
    assert stats["terminals"]==1 and stats["max_terminal_rank"]==1 and stats["clock"]==2
    assert legal(A,0,U,q,*witness)
    print("dense one-rank terminal",value,stats)
    print("small original-source cases",cases+2,"runs",6*(cases+2))

if __name__=="__main__":
    main()
