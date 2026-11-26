from itertools import combinations
from random import Random
from compact import Compression, GraphicBlock, canonical
from palette import exact
from check import kernel


def test():
    rng=Random(9021)
    total=0
    for _ in range(35):
        n=5
        p=rng.randrange(1,n)
        parts=[list(range(p)),list(range(p,n))]
        flags=[rng.randrange(2) for _ in range(3)]
        edges=[(a,b) for a,b in combinations(range(n),2) if flags[2 if (a<p)!=(b<p) else int(a>=p)]]
        A=[(1<<a)^(1<<b) for a,b in edges]
        B=[rng.randrange(1<<(n+1)) for _ in range(3)]
        if _%2==0:
            B=[A[rng.randrange(len(A))] if A else 0 for _ in range(3)]
        comp=Compression(GraphicBlock(A,edges,n,parts),B)
        found={kernel(A,B,m) for m in range(1<<len(A))}
        for K in {canonical(z for z in range(1,8) if m>>(z-1)&1) for m in range(128)}:
            out=exact(comp,K)
            assert (out is not None)==(K in found)
            if out is not None:
                assert kernel(A,B,out)==K
            total+=1
    print(total,"named-kernel decisions compared with all contracting sets")


if __name__=="__main__":
    test()
