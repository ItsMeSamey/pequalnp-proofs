"""Graphic block tables, arbitrary named kernels and forced dense demands."""
from collections import Counter
from itertools import combinations
from random import Random
from graphic import GraphicBlock
from macro import augment, canonical, functional, image, solve, spectrum


def traces(cols,roots):
    result={}
    for m in range(1<<len(cols)):
        chosen=tuple(v for i,v in enumerate(cols) if m>>i&1)
        ker=canonical(z for z in range(1<<len(roots)) if solve(chosen,image(roots,z)) is not None)
        result.setdefault(ker,m)
    return result


def run():
    rng=Random(12571)
    count=Counter()
    for _ in range(52):
        n=rng.randrange(3,7)
        p=rng.randrange(1,n)
        parts=[list(range(p)),list(range(p,n))]
        inside=[rng.randrange(2),rng.randrange(2)]
        join=rng.randrange(2)
        edges=[(i,j) for i,j in combinations(range(n),2)
               if (bool(join) if (i<p)!=(j<p) else bool(inside[int(i>=p)]))]
        if len(edges)>10:
            continue
        inc=tuple((1<<i)^(1<<j) for i,j in edges)
        # A checkerboard coordinate injection makes input and graph row labels differ.
        cols=tuple(v | ((v.bit_count()%2)<<n) | (((v & 21).bit_count()%2)<<(n+1)) for v in inc)
        block=GraphicBlock(cols,edges,n,parts)
        V=canonical(cols)
        U=tuple(rng.sample(V,min(3,len(V))))
        raw=block.table(list(enumerate(cols)),U)
        for c in range(1<<len(U)):
            u=image(U,c)
            for f in range(1<<len(U)):
                possible=any(image(cols,m)==u and functional(U+tuple(v for i,v in enumerate(cols) if m>>i&1),f) is not None for m in range(1<<len(cols)))
                assert possible==(u in raw[f])
                count["paired"]+=1
        B=tuple((image(V,rng.randrange(1<<len(V))) ^ ((1<<(n+2)) if rng.randrange(6)==0 else 0)) for _ in range(3))
        all_traces=traces(cols,B)
        spaces={canonical(z for z in range(1,8) if m>>(z-1)&1) for m in range(128)}
        for K in spaces:
            result=block.exact_kernel(B,K)
            assert (result is not None)==(K in all_traces)
            if result:
                X,reps=result
                selected=tuple(v for i,v in enumerate(cols) if X>>i&1)
                assert canonical(z for z in range(8) if solve(selected,image(B,z)) is not None)==K
                assert all(image(cols,w)==image(B,k) and not w&~X for k,w in zip(K,reps))
            count["full kernel"]+=1
    for m in (8,16,24):
        edges=list(combinations(range(m),2))
        C=tuple((0 if i==0 else 1<<(i-1))^(1<<(j-1)) for i,j in edges)
        u=(1<<(m-4))-1
        block=GraphicBlock(C,edges,m,[list(range(m))])
        D=C+(u,)
        L=(0,)*len(C)+(1,)
        M=tuple({(0,m-3):2,(0,m-2):4,(0,m-1):8}.get(e,0) for e in edges)+(0,)
        ordinary,_=augment(D,L,M,4)
        assert ordinary[:-1]==C
        spectrum0,width=spectrum(D,L,M,4,[list(range(len(C))),[len(C)]],(0,1),graphics={0:block})
        assert 3 in spectrum0
        c,d=spectrum0[3]
        assert c>>len(C)&1 and not d>>len(C)&1
        assert image(C,c)==u
        count["dense forced"]+=1
    return count


if __name__=="__main__":
    print(run())
