from random import Random
from solver import solve,marker
from two import span
rng=Random(743)
for trial in range(1200):
    n=rng.randrange(1,10)
    r=rng.randrange(1,7)
    h=[rng.randrange(1<<r) for _ in range(n)]
    a,b=([rng.randrange(4) for _ in h] for _ in range(2))
    C={x for x in range(1<<n) if not marker(h,x)}
    D=span([sum(1<<i for i,v in enumerate(h) if v>>j&1) for j in range(r)])
    want={marker(a,x)^marker(b,y) for x in C for y in D if not x&y}
    for z in range(4):
        pair=solve(h,a,b,z)
        assert (pair is not None)==(z in want)
        if pair:
            x,y=pair
            assert x in C and y in D and not x&y and marker(a,x)^marker(b,y)==z
print("4800 full arbitrary-binary target decisions and returned witnesses verified")
