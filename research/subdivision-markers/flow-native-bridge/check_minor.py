"""Check the shortened and punctured codes around native witnesses."""
from pathlib import Path
from random import Random
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/"unseeded-root-states"))
from solve import canonical, eliminate, image


def dual(rows,n):
    return canonical(eliminate([sum(((r>>j)&1)<<i for i,r in enumerate(rows)) for j in range(n)])[1])


def minor(rows, zero, retained):
    relations=eliminate([r&zero for r in rows])[1]
    return canonical(image(rows,z)&retained for z in relations)


def test():
    rng=Random(24759)
    for t in range(1200):
        n=2+t%12
        full=(1<<n)-1
        S=canonical(rng.randrange(1<<n) for _ in range(rng.randrange(n+1)))
        T=dual(S,n)
        a=rng.randrange(1<<n)
        b=rng.randrange(1<<n)&~a
        free=full^(a|b)
        P,Q=minor(S,b,free),minor(T,a,free)
        assert len(P)+len(Q)==free.bit_count()
        assert all(not((x&y).bit_count()%2) for x in P for y in Q)
    print("1200 native minors matched by dimension and orthogonality checks")


if __name__=="__main__":
    test()
