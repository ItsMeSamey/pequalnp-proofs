import random
import time
from bank import compress
from cover import System,direct
from gaussian_backend import Unsupported,backend


def family(n):
    g=[(2<<(2*i),2<<(2*i+1),0) for i in range(n//2)]
    out=sum(2<<(n+j) for j in range(len(g)))
    return g,out


def main():
    rng=random.Random(335)
    supported=0
    for _ in range(450):
        n,m=rng.randint(1,6),rng.randint(0,5)
        g=[tuple(rng.randrange(2<<(n+i)) for _ in range(3)) for i in range(m)]
        out=rng.randrange(2<<(n+m))
        system,_=compress(n,g,out,m,stages=rng.randint(0,3))
        try:
            solver=backend(system)
        except Unsupported:
            continue
        supported+=1
        for pins in range(1<<n):
            assignment=rng.randrange(1<<n)&pins
            assert solver(system,pins,assignment)==sum(direct(n,g,out,x) for x in range(1<<n) if x&pins==assignment)
        count,w=system.count_witness(solver)
        assert w is None if not count else direct(n,g,out,w)==1
    print('random certified:',supported)
    # Duplicate quadratic equations differing by an affine row; singular free direction.
    s=System(3,[(16,[(2,4)]),(32,[(4,2),(8,)])],[(16^32,)])
    assert backend(s)(s,0,0)==4
    for n in [14,18,32,64]:
        g,out=family(n)
        s,_=compress(n,g,out,0)
        start=time.perf_counter()
        total=backend(s)(s,0,0)
        elapsed=time.perf_counter()-start
        assert total==((1<<n)-(1<<(n//2)))//2
        slow=None
        if n<=18:
            start=time.perf_counter()
            assert sum(direct(n,g,out,x) for x in range(1<<n))==total
            slow=time.perf_counter()-start
        print(n,total,round(elapsed,6),slow)


if __name__=='__main__':
    main()
