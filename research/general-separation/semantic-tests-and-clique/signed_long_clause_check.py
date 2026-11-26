"""Compare both signed selector buckets to direct counts on CNFs and NBPs."""
from itertools import product
from random import Random

def clause_ok(clause, bits):
    return any(bits[abs(lit)-1] == int(lit > 0) for lit in clause)

def check(n, clauses, cutoff):
    long = [c for c in clauses if len(c) > cutoff]
    short = [c for c in clauses if len(c) <= cutoff]
    buckets = [0,0]
    direct = 0
    for bits in product((0,1), repeat=n):
        if not all(clause_ok(c,bits) for c in short):
            continue
        bad = sum(not clause_ok(c,bits) for c in long)
        found = [0,0]
        for z in product((0,1),repeat=len(long)):
            if all(not flag or not clause_ok(c,bits) for flag,c in zip(z,long)):
                parity = 0
                for b in z:
                    parity ^= b
                found[parity] += 1
        assert found == ([1,0] if bad == 0 else [2**(bad-1)]*2)
        buckets = [a+b for a,b in zip(buckets,found)]
        direct += bad == 0
    assert buckets[0]-buckets[1] == direct
    return direct

rng = Random(371)
for _ in range(200):
    n = rng.randrange(1,6)
    clauses = [tuple(rng.choice((-1,1))*rng.randrange(1,n+1)
                     for _ in range(rng.randrange(9))) for _ in range(rng.randrange(7))]
    check(n,clauses,rng.randrange(-1,4))

# Live node i queries shared input x or w, and has two successor sets.
# Represent acceptance by pinning the source and defining each node in both directions.
for _ in range(250):
    n = 3
    rows = [[(rng.randrange(1 << (n-i)) << (i+1)) for _ in (0,1)] for i in range(n)]
    labels = [rng.randrange(2) for _ in rows]
    clauses = [(3,)]
    for i, pair in enumerate(rows):
        y = i+3
        for b, mask in enumerate(pair):
            guard_neg = (labels[i]+1) * (1 if b == 0 else -1)
            if mask & (1<<n):
                clauses.append((guard_neg,y))
                continue
            succ = [j+3 for j in range(i+1,n) if mask & (1<<j)]
            clauses.extend((guard_neg,-v,y) for v in succ)
            clauses.append((guard_neg,-y,*succ))
    direct = 0
    for bits in product(range(2),repeat=2):
        truth = 1<<n
        for i in reversed(range(n)):
            if rows[i][bits[labels[i]]] & truth:
                truth |= 1 << i
        direct += truth & 1
    assert check(n+2,clauses,2) == direct
print('200 arbitrary CNFs, 250 seeded NBPs: both buckets verified per assignment')
