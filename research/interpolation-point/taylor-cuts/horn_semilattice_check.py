"""Independent truth-table and poset Möbius-inversion checks."""
from itertools import product
from random import Random
from horn_semilattice import compile_horn_residual, SupportBudgetExceeded


def holds(f,x):
    return all(any(bool((x>>(abs(l)-1))&1)==(l>0) for l in c) for c in f)


def check(n,horn,extra,rows):
    result=compile_horn_residual(n,horn,extra,rows)
    core=[x for x in range(1<<n) if holds(horn,x)]
    required={x for x in core if holds(extra,x) and all((x&m).bit_count()%2==b for m,b in rows)}
    # Independently invert the incidence matrix of the actual model-inclusion poset.
    canonical=set()
    for x in sorted(core,key=int.bit_count):
        if (x in required) != (sum(c & x == c for c in canonical)%2==1):
            canonical.add(x)
    assert result.support==canonical
    assert (result.witness in required if required else result.witness is None)
    return result


if __name__=='__main__':
    n=2
    horn_universe=[tuple(l for l in (a,b) if l) for a,b in product((0,1,-1),(0,2,-2))
                   if not(a>0 and b>0)]
    cores={}
    for mask in range(1<<len(horn_universe)):
        formula=[c for i,c in enumerate(horn_universe) if mask>>i&1]
        truth=tuple(holds(formula,x) for x in range(4))
        cores.setdefault(truth,formula)
    pairs=0
    for horn in cores.values():
        for table in range(16):
            extra=[tuple(-j if x>>(j-1)&1 else j for j in (1,2)) for x in range(4) if not(table>>x&1)]
            for mask,b in product(range(4),range(2)):
                check(2,horn,extra,[(mask,b)]);pairs+=1
    rng=Random(911)
    for _ in range(350):
        n=rng.randrange(1,8)
        horn=[]
        for i in range(rng.randrange(8)):
            neg=[-j for j in rng.sample(range(1,n+1),rng.randrange(n+1))]
            horn.append(neg+([rng.randrange(1,n+1)] if rng.randrange(2) else []))
        extra=[[rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(rng.randrange(n+2))]
               for i in range(rng.randrange(7))]
        rows=[(rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))]
        check(n,horn,extra,rows)
    check(4,[(-1,-2,3),(-3,4),(-3,-4)],[(1,2),(3,4)],[(3,1)])
    chain=[(-i,i-1) for i in range(2,81)]
    out=compile_horn_residual(80,chain,[tuple(range(1,81))],[(1<<i,1) for i in range(80)])
    assert out.witness==(1<<80)-1 and out.peak<=81
    assert len(check(9,[],[list(range(1,10))],[]).support)==511
    assert len(check(8,[],[],[(3<<(2*i),1) for i in range(4)]).support)==16
    check(0,[],[],[]);check(0,[()],[],[]);check(0,[],[()],[])
    try:compile_horn_residual(12,[],[range(1,13)],max_support=40)
    except SupportBudgetExceeded:pass
    else:raise AssertionError("support cap not enforced")
    print(f'{len(cores)} Horn model families × all 16 residual truth tables × 8 XORs = {pairs} exact canonical checks; 350 further cases, 80-variable chain and growth fixtures passed')
