from itertools import product
from random import Random
from one_defect_triangular_count import count
from quadratic_target import parity


def verify(rows,b,**kw):
    good={z for z in range(1<<len(rows)) if parity(z&b) and all(not(z>>i&1 and parity(z&r)) for i,r in enumerate(rows))}
    c,w,m=count(rows,b,**kw)
    assert c==len(good) and (w in good if good else w is None)
    assert m['peak']<=1<<(m['rank']+1+m['width'])
    return m


if __name__=='__main__':
    for rows in product(range(8),repeat=3):
        for b in range(8):
            verify(rows,b)
    rng=Random(934)
    for _ in range(150):
        n=rng.randrange(3,10)
        sets=[rng.randrange(1<<n) for i in range(rng.randrange(1,4))]
        U=[sum(((v>>i)&1)<<j for j,v in enumerate(sets)) for i in range(n)]
        rows=[sum((int(i<j)^int(i!=j and parity(u&U[j])))<<j for j in range(n)) for i,u in enumerate(U)]
        b=rng.randrange(1,1<<n)
        m=verify(rows,b,certificate=(U,sets))
        assert m['width']<=1
    for _ in range(150):
        n=rng.randrange(3,10)
        u,v,w,t=[rng.randrange(1<<n) for _ in range(4)]
        D=[((v if u>>i&1 else 0)^(t if w>>i&1 else 0))&~((1<<i)-1) for i in range(n)]
        drift=rng.randrange(1<<n)
        U=[rng.randrange(2) for _ in D]
        G=[r^(drift if c else 0) for r,c in zip(D,U)]
        m=verify(G,rng.randrange(1,1<<n),certificate=(U,[drift]))
        assert m['width']<=2
    assert count([0]*6,63,state_cap=1)[0] is None
    assert count([39,14,13,59,18,44],63)[:2]==(1,55)
    print('4096 exhaustive counts, 150 tournament inversion certificates, 150 general width-2 certificates, cap and adversary passed')
