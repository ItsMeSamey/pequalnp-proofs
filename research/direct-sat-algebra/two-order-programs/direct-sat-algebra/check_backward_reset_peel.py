from random import Random
from backward_reset_peel import peel, intersect_witness


def evaluate(n,gates,out,x):
    values=1|(x<<1)
    for j,(a,b) in enumerate(gates):
        values |= ((values&a).bit_count() & (values&b).bit_count() & 1)<<(n+j+1)
    return (out&values).bit_count()%2


def hidden(n,rng):
    state=3
    gates=[]
    for j in range(n+2):
        control=(rng.randrange(1,1<<n)<<1)|rng.randrange(2)
        drift=rng.randrange(1<<(n+1))
        gates.append((state^control,state))
        state ^= (1<<(n+j+1)) ^ drift
    return gates,state


rng=Random(597)
for i in range(70):
    n=7
    g,o=hidden(n,rng)
    h,p=hidden(n,rng)
    f=peel(n,g,o)
    t=peel(n,h,p)
    assert f is not None and t is not None
    matches=[]
    for x in range(1<<n):
        value=evaluate(n,g,o,x)
        assert sum(all(not ((eq&(1|(x<<1))).bit_count()%2) for eq in rows.values()) for rows in f)==value
        if value and evaluate(n,h,p,x): matches.append(x)
    w=intersect_witness(f,t)
    assert (w is None)==(not matches)
    if w is not None: assert w in matches
print("70 recoded chain pairs, 8960 exhaustive original-input comparisons")
