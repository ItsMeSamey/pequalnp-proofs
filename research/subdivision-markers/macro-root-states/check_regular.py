"""Both quotient orientations checked against physical enumeration."""
from collections import Counter
from itertools import combinations
from random import Random
from macro import canonical, eliminate, functional, image
from regular_state import homogeneous_query, dual_query, solve_regular_state


def exact_host(H,L,M,p,t):
    cycles=eliminate(H)[1]
    width=max((v.bit_length() for v in H),default=0)
    rows=canonical(sum(((v>>j)&1)<<i for i,v in enumerate(H)) for j in range(width))
    cuts=[image(rows,i) for i in range(1<<len(rows))]
    for i in range(1<<len(cycles)):
        c=image(cycles,i)
        for d in cuts:
            if not c&d and image(L,c)^image(M,d)==p:
                return c,d
    return None


def test():
    rng=Random(4903)
    counts=Counter()
    for _ in range(40):
        n=rng.randrange(5,10)
        A=tuple(rng.randrange(32) for _ in range(n))
        basis=canonical(A)
        if len(basis)<4:
            continue
        U=tuple(rng.sample(basis,4))
        for _ in range(9):
            coord=rng.randrange(1,16)
            f=rng.choice([f for f in range(1,16) if not (f&coord).bit_count()%2])
            u=image(U,coord)
            ok=any(image(A,m)==u and functional(U+tuple(v for i,v in enumerate(A) if m>>i&1),f) is not None for m in range(1<<n))
            for reverse in (False,True):
                used=[]
                def oracle(*args):
                    used.append(1)
                    if reverse and len(used)==1:
                        return "unsupported"
                    return exact_host(*args)
                result=solve_regular_state(list(enumerate(A)),U,coord,f,oracle)
                assert (result is not None)==ok
                counts["dual" if reverse else "primal"]+=1
                if ok:
                    assert image(A,result)==u and functional(U+tuple(v for i,v in enumerate(A) if result>>i&1),f) is not None
    edges=list(combinations(range(8),2))
    A=tuple((0 if i==0 else 1<<(i-1))^(1<<(j-1)) for i,j in edges)
    U=(15,16,32,64)
    H,*_=homogeneous_query(A,U,1,2)
    five=[z for z,(i,j) in enumerate(edges) if j<=4]
    assert len(canonical(H[z] for z in five))==3 and len({H[z] for z in five})==7
    H2=tuple((v & ~(32|64)) ^ (15 if v&1 else 0) for v in A)
    assert len(canonical(H2[z] for z in five))==3 and len({H2[z] for z in five})==7
    J,*_=homogeneous_query(*dual_query(A,U,1,2))
    rank=lambda a: len(canonical(a))
    subsets=[0,(1<<len(A))-1]+[rng.randrange(1<<len(A)) for _ in range(198)]
    for m in subsets:
        assert rank(v for i,v in enumerate(J) if m>>i&1)==m.bit_count()+rank(v for i,v in enumerate(H2) if not m>>i&1)-rank(H2)
    D=A+(15,)
    L=(0,)*len(A)+(1,)
    M=tuple({(0,5):2,(0,6):4,(0,7):8}.get(e,0) for e in edges)+(0,)
    c=(1<<len(A))|(1<<edges.index((1,2)))|(1<<edges.index((3,4)))
    d=sum(((v>>4)&1)<<i for i,v in enumerate(D))
    assert not c&d and not image(D,c) and image(L,c)^image(M,d)==3
    return counts


if __name__=="__main__":
    print(test())
