from random import Random
from tournament_neutral_shore import compile_shore,lift
from quadratic_target import parity


def test(M,U,L,pins):
    V,p,R=compile_shore(M,U,L,pins)
    def legal(rows,x):
        return all(not(x>>i&1 and parity(r&x)) for i,r in enumerate(rows))
    def read(L,x):
        return sum(parity(r&x)<<i for i,r in enumerate(L))
    want={(sum(((z>>v)&1)<<i for i,v in enumerate(V)),read(L,z)) for z in range(1<<len(M))
          if all(z>>i&1 for i in pins) and legal(M,z)}
    got=set()
    for (D,T),path in R.items():
        for y in range(1<<len(V)):
            if y&p!=p or not legal(D,y):
                continue
            z=lift(M,U,V,path,y)
            t=read(T,y)
            assert legal(M,z) and read(L,z)==t and all(z>>i&1 for i in pins)
            got.add((y,t))
    assert got==want


if __name__=='__main__':
    rng=Random(311)
    for _ in range(600):
        n=rng.randrange(9)
        perm=rng.sample(range(n),n)
        u=rng.randrange(n+1)
        U,V=perm[:u],perm[u:]
        M=[0]*n
        for a,i in enumerate(perm):
            M[i]|=(1 if a<u else rng.randrange(2))<<i
            for b in range(a+1,n):
                j=perm[b]
                orient=1 if b<u else rng.randrange(2)
                M[i]|=orient<<j
                M[j]|=(1^orient)<<i
        L=[rng.randrange(1<<n) for _ in range(rng.randrange(5))]
        test(M,U,L,rng.sample(V,rng.randrange(len(V)+1)))
    print('600 complete outside projection and all readout fibers checked, with physical pins and original witness lifts')
