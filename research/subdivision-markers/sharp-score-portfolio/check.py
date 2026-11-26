"""Exercise the entire compressor with opposite and arbitrary actual witnesses."""
from collections import Counter
from random import Random
from solver import compress, decompose, elimination, linear, signature, xor


def sample_chart(rng,t,extra=True):
    m=5+2*rng.randrange(4)
    N=[]
    for _ in range(m-1):
        row=rng.randrange(1<<(m-1))
        N.append(row | ((row.bit_count()%2)<<(m-1)))
    N.append(xor(N))
    full=(1<<m)-1
    R=[(r<<1)|1 for r in N]+[full<<1]
    nr=len(R)
    base=[1<<i for i in range(nr)]+[sum(((r>>j)&1)<<i for i,r in enumerate(R))
                                      for j in range(nr)]
    L=[rng.randrange(1<<t) for _ in base]
    M=[rng.randrange(1<<t) for _ in base]
    A=full | (1<<nr)
    B=((1<<len(base))-1)^A
    seeds={signature((A,B),L,M):(A,B), signature((B,A),L,M):(B,A)}
    if extra:
        seeds[0]=(0,0)
    return base,L,M,seeds


def verify(base,L,M,seeds,t,stats):
    deleted,contracted,answer=compress(base,L,M,seeds,t,stats)
    active=((1<<len(base))-1)^(deleted|contracted)
    assert not deleted&contracted and set(answer)==set(seeds)
    assert active.bit_count()<=len(seeds)*(len(seeds)-1)//2 * (1<<max(0,t-1))
    r=max((v.bit_length() for v in base),default=0)
    cut_rows=[sum(((v>>j)&1)<<i for i,v in enumerate(base)) for j in range(r)]
    for q,(c,d) in answer.items():
        assert not (c&d or c&deleted or d&contracted) and not linear(base,c)
        assert signature((c,d),L,M)==q
        assert len(elimination(cut_rows)[0])==len(elimination(cut_rows+[d])[0])
    return active.bit_count()


def test():
    rng=Random(693)
    stats=Counter()
    compared=0
    for i in range(220):
        t=1+i%4
        base,L,M,seeds=sample_chart(rng,t,i%3!=0)
        verify(base,L,M,seeds,t,stats)
        compared+=1
    for i in range(100):
        t=1+i%3
        n=4+i%6
        base=[rng.randrange(1<<(n//2)) for _ in range(n)]
        L=[rng.randrange(1<<t) for _ in base]
        M=[rng.randrange(1<<t) for _ in base]
        kernels=elimination(base)[1]
        seeds={}
        for _ in range(150):
            c=linear(kernels,rng.randrange(1<<len(kernels)))
            a=rng.randrange(1<<(n//2))
            d=sum(((v&a).bit_count()%2)<<j for j,v in enumerate(base))
            if not c&d:
                seeds[signature((c,d),L,M)]=(c,d)
        if seeds:
            keys=list(seeds)
            rng.shuffle(keys)
            seeds={k:seeds[k] for k in keys[:3]}
        verify(base,L,M,seeds,t,stats)
        compared+=1
    for i in range(60):
        base,L,M,seeds=sample_chart(rng,4)
        offsets=[1,3] if i%2 else [8]
        named={q^offsets[0]:pair for q,pair in seeds.items()}
        deleted,contracted,answer=compress(base,L,M,named,4,stats,offsets)
        H=elimination(offsets)[0]
        cnt=len({decompose(H,q)[0] for q in named})
        bound=cnt*(cnt-1)//2 * (1<<(4-len(H)-1))
        assert len(base) - (deleted|contracted).bit_count() <= bound
        for q,(c,d) in answer.items():
            assert not(c&d or c&deleted or d&contracted) and not linear(base,c)
            assert not decompose(H,q^signature((c,d),L,M))[0]
    chart=[11,19,7]
    L=[0,0,0,8,1,1,1,2]
    M=[0,4,4,0,0,0,0,0]
    candidates={7:[],12:[]}
    for x in range(8):
        for y in range(32):
            c=(y<<3)|sum(((v&y).bit_count()%2)<<i for i,v in enumerate(chart))
            d=x|(linear(chart,x)<<3)
            q=signature((c,d),L,M)
            if q in candidates and not c&d:
                candidates[q].append((c,d))
    assert len(candidates[7])==len(candidates[12])==1
    left,right=candidates[7][0],candidates[12][0]
    assert left==right[::-1] and left[0]|left[1]==255
    print(compared,"base runs; 60 offset runs; sharp eight-element example;",dict(stats))


if __name__=="__main__":
    test()
