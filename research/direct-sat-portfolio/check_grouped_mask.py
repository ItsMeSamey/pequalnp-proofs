from random import Random
from grouped_mask import solve,estimate,certificate


def brute(n,g,o):
    good=[]
    for x in range(1<<n):
        w=1|(x<<1)
        for j,(a,b) in enumerate(g):
            if (a&w).bit_count()%2 and (b&w).bit_count()%2:
                w|=1<<(1+n+j)
        if (w&o).bit_count()%2:
            good.append(x)
    return good


def check(n,g,o):
    val=brute(n,g,o)
    budget=estimate(n,g,o)
    assert solve(n,g,o,budget=budget-1)['status']=='skip'
    out=solve(n,g,o,budget=budget)
    assert out['cost']['accepting_assignments']==len(val)
    assert out['status']==('sat' if val else 'unsat')
    assert not val or out['witness'] in val
    assert out['cost']['masks']==out['cost']['counts']*out['cost']['masks_per_count']<=budget


if __name__=='__main__':
    rng=Random(337)
    for _ in range(450):
        n=rng.randrange(6)
        g=[tuple(rng.randrange(1<<(n+j+1)) for _ in range(2)) for j in range(rng.randrange(7))]
        check(n,g,rng.randrange(1<<(1+n+len(g))))
    n=9
    g=[(1<<(1+2*j),1<<(2+2*j)) for j in range(4)]+[(15<<(n+1),1<<n)]
    assert certificate(n,g,1<<(n+5))[3]==7
    check(n,g,1<<(n+5))
    print('450 seeded original count/witness and cap checks; repeated effect columns yield 7 masks versus 32')
