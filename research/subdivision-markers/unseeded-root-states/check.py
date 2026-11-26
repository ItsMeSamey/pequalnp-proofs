"""Compare the algebraic state with all raw cycle/cocycle pairs."""
from random import Random
from solve import canonical, eliminate, image, spectrum


def span(gens):
    ans=[0]
    for x in gens:
        ans.extend([a^x for a in ans])
    return ans


def direct(base,L,M):
    cycles=span(eliminate(base)[1])
    rows=[sum(((v>>j)&1)<<i for i,v in enumerate(base))
          for j in range(max((v.bit_length() for v in base),default=0))]
    cuts=span(canonical(rows))
    return {image(L,c)^image(M,d) for c in cycles for d in cuts if not c&d}


def run(spectrum=spectrum):
    rng=Random(9913)
    for trial in range(150):
        n=trial%9
        r=trial%5
        t=trial%4
        base=[rng.randrange(1<<r) for _ in range(n)]
        L=[rng.randrange(1<<t) for _ in base]
        M=[rng.randrange(1<<t) for _ in base]
        found,_,_=spectrum(base,L,M,t)
        assert set(found)==direct(base,L,M)
    chart=[11,19,7]
    base=[1,2,4]+[sum(((r>>i)&1)<<j for j,r in enumerate(chart)) for i in range(5)]
    L=[0,0,0,8,1,1,1,2]
    M=[0,4,4,0,0,0,0,0]
    core,w,p=spectrum(base,L,M,4)
    assert set(core)==set(range(16))-{14}
    full,w2,p2=spectrum(base+[8],L+[0],M+[1],4)
    assert set(full)==set(range(16)) and 14 in full
    print("150 direct mask comparisons; 8-element core then coloop:",(w,p),(w2,p2))
    for n in (10,32,64):
        base=[(1<<(n-1))-1]+[1<<i for i in range(n-1)]
        L=[1]+[0]*(n-1)
        M=[0,2,4,8]+[0]*(n-4)
        found,w,p=spectrum(base,L,M,4)
        assert set(found)=={0,1,2,4,6,8,10,12,14}
        print("circuit",n,"rank",n-1,"port width",w,"peak states",p)


if __name__=='__main__':
    from pairs import spectrum as paired
    print("Subspace states:")
    run()
    print("Paired states:")
    run(paired)
    rng=Random(931)
    for j in range(60):
        n=1+j%8
        leaves=list(range(n))
        rng.shuffle(leaves)
        while len(leaves)>1:
            leaves.append((leaves.pop(0),leaves.pop(0)))
        base=[rng.randrange(16) for _ in range(n)]
        L=[rng.randrange(8) for _ in base]
        M=[rng.randrange(8) for _ in base]
        found,_,_=paired(base,L,M,3,leaves[0])
        assert set(found)==direct(base,L,M)
    print("60 additional supplied permuted layouts passed")
