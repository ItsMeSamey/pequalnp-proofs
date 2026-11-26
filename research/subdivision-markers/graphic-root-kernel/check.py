"""Independent named-kernel comparisons after forward and reverse physical lifting."""
from itertools import combinations
from random import Random
from compact import Compression, GraphicBlock, canonical, image, solve


def kernel(cols, roots, X):
    chosen=tuple(v for i,v in enumerate(cols) if X>>i&1)
    return canonical(z for z in range(1<<len(roots)) if solve(chosen,image(roots,z)) is not None)


def test():
    rng=Random(1073)
    checks=0
    for trial in range(22):
        n=7+trial%4
        p=n//2
        joined=bool(trial%2)
        parts=[list(range(p)),list(range(p,n))]
        edges=[(i,j) for i,j in combinations(range(n),2) if (joined if (i<p)!=(j<p) else bool((trial+int(i>=p))%3))]
        if edges and trial%3==0:
            edges += [edges[0],(0,0)]
        cols=[(1<<a)^(1<<b) for a,b in edges]
        src=GraphicBlock(cols,edges,n,parts)
        V=canonical(cols)
        B=[image(V,rng.randrange(1<<len(V)))^(1<<(n+1) if r==2 and trial%3 else 0) for r in range(3)]
        if trial%5==0:
            B.append(B[0]^B[1])
        cm=Compression(src,B)
        for back in (False,True):
            c1,c2=(cm.reduced.cols,src.cols) if back else (src.cols,cm.reduced.cols)
            b1,b2=(cm.smallroots,B) if back else (B,cm.smallroots)
            for i in range(22):
                mask=(0 if i==0 else (1<<len(c1))-1 if i==1 else rng.randrange(1<<len(c1)))
                out=cm.transfer(mask,back)
                assert kernel(c1,b1,mask)==kernel(c2,b2,out)
                checks+=1
    # Compression is nontrivial on repeated dense types and independent classes.
    for connected in (False,True):
        n=44
        parts=[list(range(22)),list(range(22,44))]
        edges=[(a,b) for a,b in combinations(range(n),2) if (a<22)!=(b<22) or connected]
        C=[(1<<a)^(1<<b) for a,b in edges]
        src=GraphicBlock(C,edges,n,parts)
        B=[(1<<22)-1, ((1<<22)-1)<<22, 1<<n]
        cm=Compression(src,B)
        assert cm.dim==2 and cm.reduced.n==12
        for back in (False,True):
            a,b=(cm.reduced.cols,C) if back else (C,cm.reduced.cols)
            x,y=(cm.smallroots,B) if back else (B,cm.smallroots)
            for _ in range(5):
                pick=rng.sample(range(len(a)), min(rng.randrange(6,22),len(a)))
                mask=sum(1<<i for i in pick)
                assert kernel(a,x,mask)==kernel(b,y,cm.transfer(mask,back))
                checks+=1
    print(checks,"full-kernel transfers; K44 and K22,22 both reduced from 44 vertices to 12")


if __name__=="__main__":
    test()
