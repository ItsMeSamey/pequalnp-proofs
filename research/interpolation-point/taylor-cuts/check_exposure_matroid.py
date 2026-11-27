"""Small exhaustive original-graph tests for eligible exposures and reservoir extension."""
from functools import lru_cache
from itertools import combinations,permutations
from random import Random


def bits(mask):
    while mask:
        x=mask&-mask
        yield x
        mask^=x


def exposure_family(n,edges):
    neighbors=[0]*n
    for u,v in edges:
        neighbors[u]|=1<<v
        neighbors[v]|=1<<u
    @lru_cache(None)
    def perfect(rem):
        if not rem:
            return True
        x=rem&-rem
        return any(perfect(rem^x^y) for y in bits(neighbors[x.bit_length()-1]&rem))
    V=(1<<n)-1
    return {h for h in range(V+1) if perfect(V^h)}


def obstruction(bases):
    for a in bases:
        for b in bases:
            for x in bits(a&~b):
                if not any((a^x^y) in bases for y in bits(b&~a)):
                    return a,b,x
    return None


def audit(n,edges,eligible):
    full=exposure_family(n,edges)
    delta=min(h.bit_count() for h in full)
    assert obstruction({h for h in full if h.bit_count()==delta}) is None
    calls=0
    for P in eligible:
        allowed={h for h in full if not h&~P}
        if not allowed:
            continue
        sizes={h.bit_count() for h in allowed}
        assert sizes==set(range(min(sizes),max(sizes)+1,2))
        for k in {min(sizes),max(sizes)}:
            assert obstruction({h for h in allowed if h.bit_count()==k}) is None
            calls+=1
    return calls


def reservoir(n,edges,P,k,exceptional,generic,adj):
    feasible=exposure_family(n,edges)
    candidates={h for h in feasible if not h&~P and h.bit_count()==k}
    neighborhoods={v:(adj[v] if exceptional>>v&1 else generic) for v in range(n) if P>>v&1}
    actual={}
    for h in candidates:
        ports=[v for v in neighborhoods if h>>v&1]
        actual[h]=any(all(neighborhoods[v]>>r&1 for v,r in zip(ports,rs)) for rs in permutations(range(k)))
    by_subset={}
    for h,ok in actual.items():
        assert by_subset.setdefault(h&exceptional,ok)==ok
    joined=list(edges)+[(v,n+r) for v,nb in neighborhoods.items() for r in range(k) if nb>>r&1]
    assert any(actual.values())==(0 in exposure_family(n+k,joined))
    return actual


if __name__=='__main__':
    endpoints=instances=0
    for n in range(5):
        pairs=list(combinations(range(n),2))
        for mask in range(1<<len(pairs)):
            es=[e for i,e in enumerate(pairs) if mask>>i&1]
            endpoints+=audit(n,es,range(1<<n))
            instances+=1
    rng=Random(748)
    for i in range(100):
        n=rng.randrange(5,9)
        es=[e for e in combinations(range(n),2) if rng.randrange(3)==0]
        endpoints+=audit(n,es,[(1<<n)-1,0,*[rng.randrange(1<<n) for j in range(5)]])
        instances+=1
    tri=[(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
    assert min(map(int.bit_count,exposure_family(6,tri)))==2
    outcomes=reservoir(6,tri,0b111111,2,0b001001,0b01,{0:0b10,3:0})
    assert sum(outcomes.values())==2 and len(outcomes)==9
    for i in range(52):
        n=5+i%2
        es=[e for e in combinations(range(n),2) if rng.randrange(2)]
        P=rng.randrange(1<<n)
        k=rng.randrange(4)
        exc=P&rng.randrange(1<<n)
        reservoir(n,es,P,k,exc,rng.randrange(1<<k),{v:rng.randrange(1<<k) for v in range(n)})
    middle={h for h in exposure_family(4,[(0,1),(1,2),(2,3)]) if h.bit_count()==2}
    assert middle=={0b0011,0b1001,0b1100}
    assert all((0b0011^1^y) not in middle for y in bits(0b1100))
    print(instances,'graphs;',endpoints,'nonempty endpoint layers; 53 reservoir controls; P4 exchange obstruction passed')
