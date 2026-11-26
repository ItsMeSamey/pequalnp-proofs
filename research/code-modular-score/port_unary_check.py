"""Check monochrome three-line gluing and dual preimage on small actual codes."""
from random import Random
from itertools import product

rng=Random(19174)
def span(rows):
    v={0}
    for r in rows:
        v |= {x^r for x in v}
    return v
def parity(x): return x.bit_count()%2
def L(t):
    return ((parity(t&3)) | (parity(t&6)<<1) | (parity(t&5)<<2))
def ortho(c,n): return {z for z in range(1<<n) if not any(parity(z&x) for x in c)}
def glue(c,n,d,m):
    return {(x>>3) | ((y>>3)<<n) for x in c for y in d if x%8==y%8}
for trial in range(100):
    c=span([7]+[rng.randrange(64) for _ in range(5)])
    # Two real coordinates per line; identical nonzero q-bit forces even
    # in that component, or free q/one active q-column per trial.
    rows=[rng.randrange(4) for _ in range(3)]
    def valid(x): return not any(parity((x>>(2*i))&rows[i]) for i in range(3))
    def groups(x): return sum(parity((x>>(2*i))&3)<<i for i in range(3))
    d={t | (x<<3) for x in range(64) if valid(x) for t in (groups(x),groups(x)^7)}
    actual=glue(c,3,d,6)
    unary={(y>>3)|(x<<3) for x in range(64) if valid(x) for y in c if y%8==groups(x)}
    assert unary==actual
    dc,dd=ortho(c,6),ortho(d,9)
    def pre(z,n):
        return {t|(x<<3) for x in range(1<<n) for t in range(8) if L(t)|(x<<3) in z}
    assert glue(pre(dc,3),3,pre(dd,6),6)==ortho(actual,9)
print('100 direct unary and dual-preimage code tables matched')
