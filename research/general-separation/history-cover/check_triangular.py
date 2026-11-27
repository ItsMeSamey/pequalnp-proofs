from random import Random
from cover import System,direct
from bank import compress
from triangular_backend import backend
from character_backend import backend as old, Unsupported


def run():
    rng=Random(748)
    for k in [4,12,64]:
        n=k+1
        defs=[]
        for j in range(k):
            prior=2<<(n+j-1) if j else 0
            defs.append((2<<(n+j),[(2<<j,2<<(j+1)),(prior,)]))
        s=System(n,defs,[(defs[-1][0],)])
        assert old(s,k).rank==k
        c=backend(s,1)
        assert c.rank==1 and not c.retained
        if n<=13:
            assert c(s,0,0)==s.count_witness()[0]
        print(k,c.rank,c(s,0,0))
    for _ in range(300):
        n=rng.randrange(1,5); m=rng.randrange(1,7)
        g=[tuple(rng.randrange(2<<(n+i)) for _ in range(3)) for i in range(m)]
        out=rng.randrange(2<<(n+m))
        s,_=compress(n,g,out,m,stages=m)
        c=backend(s,m+1)
        for pins in range(1<<n):
            a=pins&rng.randrange(1<<n)
            assert c(s,pins,a)==sum(direct(n,g,out,x) for x in range(1<<n) if x&pins==a)
    # Cubic producer chain requires retaining the shared product.
    s=System(3,[(16,[(2,4)]),(32,[(16,8)])],[(32,)])
    c=backend(s,2)
    assert c.retained==1 and c(s,0,0)==1
    print('300 random originals and cubic refusal passed')


if __name__=='__main__':
    run()
