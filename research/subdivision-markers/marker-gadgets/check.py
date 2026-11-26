"""Exact full-witness and projected-witness comparisons for pin compression."""
from itertools import combinations
from random import Random

def even(rows,x):
    return all(not (x>>i&1) or (row&x).bit_count()%2==0 for i,row in enumerate(rows))

def reachable(rows,start,forbidden):
    seen = 1<<start
    while True:
        more = seen
        for i,r in enumerate(rows):
            if seen>>i&1:
                more |= r & ~forbidden
        if seen == more:
            return seen
        seen = more

def mandatory(rows,a,b):
    pins = (1<<a)|(1<<b)
    if not rows[a]>>b&1:
        return pins
    rem = rows[:]
    rem[a] ^= 1<<b
    rem[b] ^= 1<<a
    if not reachable(rem,a,0)>>b&1:
        return None
    return pins | sum(1<<v for v in range(len(rows)) if v not in (a,b)
                      and not reachable(rem,a,1<<v)>>b&1)

def serial(original,blocks):
    """Blocks are (marker-support mask, target), disjoint in the original graph."""
    n = len(original)
    k = len(blocks)
    rows = list(original)+[0]*(k+3)
    a,b = n+k+1,n+k+2
    def edge(i,j):
        assert i!=j and not rows[i]>>j&1
        rows[i] |= 1<<j
        rows[j] |= 1<<i
    edge(a,b)
    edge(a,n)
    edge(b,n+k)
    for i,(m,h) in enumerate(blocks):
        if not h:
            edge(n+i,n+i+1)
        for j in range(n):
            if m>>j&1:
                edge(j,n+i)
                edge(j,n+i+1)
    return rows,(1<<a)|(1<<b)

def compare(rows,blocks):
    G,pins = serial(rows,blocks)
    n = len(rows)
    expected = {x for x in range(1<<n) if even(rows,x) and
                all((x&m).bit_count()%2==h for m,h in blocks)}
    full = [s for s in range(1<<len(G)) if s & pins == pins and even(G,s)]
    extension = ((1<<len(G))-1) ^ ((1<<n)-1)
    assert set(full) == {x|extension for x in expected}

if __name__ == '__main__':
    count = 0
    for n in range(2,6):
        es = list(combinations(range(n),2))
        for code in range(1<<len(es)):
            rows = [0]*n
            for j,(a,b) in enumerate(es):
                if code>>j&1:
                    rows[a] |= 1<<b
                    rows[b] |= 1<<a
            valid = [s for s in range(1<<n) if even(rows,s)]
            for a,b in es:
                pins = (1<<a)|(1<<b)
                active = [s for s in valid if s&pins==pins]
                forced = None
                if active:
                    forced = (1<<n)-1
                    for s in active:
                        forced &= s
                assert mandatory(rows,a,b)==forced
                count += 1
    print(count,'mandatory-set comparisons',flush=True)
    rng = Random(68212)
    for _ in range(500):
        n = rng.randrange(0,8)
        k = rng.randrange(1,5)
        owners = [rng.randrange(k) for i in range(n)]
        rows = [0]*n
        for a,b in combinations(range(n),2):
            if owners[a]==owners[b] and rng.randrange(2):
                rows[a] |= 1<<b
                rows[b] |= 1<<a
        blocks = [(sum(1<<j for j in range(n) if owners[j]==i and rng.randrange(2)),rng.randrange(2)) for i in range(k)]
        compare(rows,blocks)
    print('500 exact serial-extension comparisons')
    rows,pins = serial([2,1],[(1,1),(2,1)])
    s = ((1<<len(rows))-1)^(1<<3)
    assert s & pins == pins and even(rows,s) and not even([2,1],3)
    print('Cross-block edge obstruction validated')
