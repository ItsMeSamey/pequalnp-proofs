#!/usr/bin/env python3
"""Implicit positive-moment peeling and primal-dual raw-clause group cover."""
from fractions import Fraction as F
from random import Random


def algorithm(m,groups,cost,penalty,moment):
    selected=set()
    paid={}
    dual={}
    overlap=0
    while True:
        forbidden=0
        for j in selected:
            forbidden |= groups[j]
        def upward(mask):
            total=sum(moment(mask | (1<<i),forbidden) for i in range(m))
            return total-sum(v.bit_count()*h for v,h in paid.items()
                             if not v&forbidden and v&mask==mask)
        mass=upward(0)
        if not mass:
            break
        v=0
        for i in range(m):
            candidate=v | (1<<i)
            probe=upward(candidate)
            if probe>0:
                v,mass=candidate,probe
        assert v and v not in dual and mass%v.bit_count()==0
        h=mass//v.bit_count()
        covers=[j for j,g in enumerate(groups) if v&g]
        overlap=max(overlap,len(covers))
        slack={j:cost[j]-sum(y for w,y in dual.items() if w&groups[j]) for j in covers}
        increment=min([penalty]+list(slack.values()))
        assert increment>=0
        dual[v]=increment
        # Prefer the penalty on ties to exercise later coverage of a paid point.
        if increment==penalty:
            paid[v]=h
        else:
            selected.add(next(j for j in covers if slack[j]==increment))
    remaining={v:h for v,h in paid.items() if not v&forbidden}
    answer=moment(0,forbidden)-sum(remaining.values())
    spent=sum(cost[j] for j in selected)+penalty*len(paid)
    assert spent <= (overlap+1)*sum(dual.values())
    return answer,spent,paid,remaining,dual


def main():
    rng=Random(632811)
    later=0
    for case in range(180):
        m=rng.randrange(1,7)
        groups=[rng.randrange(1,1<<m) for _ in range(rng.randrange(8))]
        costs=[F(rng.randrange(1,20),rng.randrange(1,4)) for _ in groups]
        penalty=F(rng.randrange(1,10),rng.randrange(1,4))
        weights={v:rng.choice((0,1,3,2**132+1)) for v in
                 rng.sample(range(1<<m),rng.randrange(1,(1<<m)+1))}
        def moment(mask,forbidden):
            return sum(h for v,h in weights.items() if v&mask==mask and not v&forbidden)
        answer,spent,paid,remaining,dual=algorithm(m,groups,costs,penalty,moment)
        assert answer==weights.get(0,0)
        assert all(h==weights[v] for v,h in paid.items())
        assert all(0<=y<=penalty for y in dual.values())
        assert all(sum(y for v,y in dual.items() if v&g)<=cost for g,cost in zip(groups,costs))
        opt=None
        for choice in range(1<<len(groups)):
            covered=0
            value=0
            for j,g in enumerate(groups):
                if choice>>j&1:
                    covered |= g
                    value+=costs[j]
            value+=penalty*sum(h>0 and bool(v) and not(v&covered) for v,h in weights.items())
            opt=value if opt is None else min(opt,value)
        degree=max((sum(bool(v&g) for g in groups) for v,h in weights.items() if v and h),default=0)
        assert sum(dual.values())<=opt and spent<=(degree+1)*opt
        later+=len(paid)-len(remaining)
    assert later>0
    print(f"180 exact weighted cover cases passed; {later} previously paid patterns were later covered.")


if __name__=='__main__':
    main()
