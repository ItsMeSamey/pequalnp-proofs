"""Defensive lower bound for pure-shore preprocessing, on singleton footprints only."""
from itertools import combinations, permutations

pts=[p for p in range(1,8) if p!=1]
lines=[l for l in range(1,8) if l!=2]
def incident(p,l):
    return (p&l).bit_count()%2==0
assert any(all(incident(p,l) for p,l in zip(pts,order)) for order in permutations(lines))

def check(stars):
    raw=frozenset(1<<i for i in range(6))
    def new(S):
        # Empty or repeated masks cannot enable a new singleton trace.
        return {h for u,v in combinations(S,2) for h in (u|v,u&v) if h and h not in S}
    for t in range(1,5):
        maximum=0;total=0
        for triples in combinations([s for s in stars if s.bit_count()==3],t):
            target=frozenset(triples)
            pairs={h for s in stars-target for h in range(1,64)
                   if h.bit_count()==2 and h&s==h}
            def close(S):
                while eligible:=new(S)&target:S=S|eligible
                return frozenset(S)
            states={close(raw|pairs)}
            for _ in range(t-1):
                states={close(s|{h}) for s in states for h in new(s)-target}
            maximum=max(maximum,max(len(s&target) for s in states))
            total+=len(states)
        assert maximum<t
        print(t,total,maximum)

check(frozenset(sum(1<<j for j,l in enumerate(lines) if incident(p,l)) for p in pts))
check(frozenset(sum(1<<i for i,p in enumerate(pts) if incident(p,l)) for l in lines))
