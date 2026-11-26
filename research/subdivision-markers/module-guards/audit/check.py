from itertools import combinations
from random import Random


def par(x):
    return x.bit_count() & 1


def local(rows, offsets, x, h):
    return all(not (x>>i&1) or (par(r&x) ^ (offsets>>i&1) ^ h)==0
               for i,r in enumerate(rows))


def mul(a,b):
    p=set()
    for u in a:
        for v in b:
            uv=tuple(sorted(u+v))
            p.symmetric_difference_update([uv])
    return p


def linear(mask):
    return {(i,) for i in range(mask.bit_length()) if mask>>i&1}


def evaluate_formal_identity(Y,C,H,T):
    one={()}
    R=mul(Y,one^H)
    child=mul(C,one^H^T)
    quotient=mul(C,one^T)
    assert mul(R,child)^mul(R,quotient)==mul(mul(Y,C),H^mul(H,H))
    assert mul(R,one^Y)==mul(one^H,Y^mul(Y,Y))
    for L in (H,Y,C):
        assert mul(L,L)^L=={(i,i) for i, in L}^L


def run():
    rng=Random(14761)
    typed=0
    for n in range(1,5):
        pairs=list(combinations(range(n),2))
        for edge in range(1<<len(pairs)):
            rows=[0]*n
            for j,(a,b) in enumerate(pairs):
                if edge>>j&1:
                    rows[a]|=1<<b
                    rows[b]|=1<<a
            for d in range(1<<n):
                for h in (0,1):
                    good={ (par(x&~d),par(x&d)) for x in range(1<<n) if local(rows,d,x,h)}
                    matching=d if h else ((1<<n)-1)^d
                    predicted={(0,0)}
                    if matching:
                        predicted.add((1-h,h))
                    assert good==predicted
                    typed+=1
    shared=0
    for _ in range(1000):
        n=rng.randrange(1,9)
        rows=[rng.getrandbits(n)&~(1<<i) for i in range(n)]
        d=rng.getrandbits(n)
        A=set()
        for h in (0,1):
            states={par(x) for x in range(1<<n) if local(rows,d,x,h)}
            assert 0 in states
            if 1 in states:
                A.add(h)
        assert A and {d>>i&1 for i in range(n)}<=A
        shared+=1
    formal=0
    for _ in range(600):
        masks=[rng.getrandbits(6) for _ in range(4)]
        evaluate_formal_identity(*(linear(i) for i in masks))
        formal+=1
    print(typed,'exact typed interfaces;',shared,'directed parity interfaces;',formal,'formal PC product identities passed')


if __name__=='__main__':
    run()
