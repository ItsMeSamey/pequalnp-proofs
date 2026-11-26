"""Independent finite audit of projected Rado budgets on two-dimensional interfaces."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from random import Random

K = 15                         # bit v denotes vector v, including zero
LINES = (3, 5, 9)
SUBS = (1, *LINES, K)
POINTER = {v:i for i,v in enumerate(SUBS)}
NEG = -100
FULL = 15                      # here bit x denotes an interface assignment
HALF = {line:tuple(sum(1 << x for x in range(4)
                      if (x & (line.bit_length()-1)).bit_count()%2 == b) for b in (0,1))
        for line in LINES}


def members(space):
    while space:
        bit = space & -space
        yield bit.bit_length()-1
        space ^= bit


@lru_cache(maxsize=20000)
def join(a,b):
    total = 0
    for u in members(a):
        for v in members(b):
            total |= 1 << (u ^ v)
    return total


def dim(s):
    return s.bit_count().bit_length()-1


@lru_cache(maxsize=50000)
def profile(spaces):
    # For each full subfamily span, retain the largest cardinality having that span.
    counts = {1:0}
    for space in spaces:
        out = counts.copy()
        for old,size in counts.items():
            new = join(old,space)
            out[new] = max(out.get(new,0),size+1)
        counts = out
    result = [NEG]*5
    for span,n in counts.items():
        j = POINTER[span & K]
        result[j] = max(result[j], n-dim(span))
    return tuple(result)


def budget(pr,L):
    return max(x+dim(B&L) for B,x in zip(SUBS,pr))


@lru_cache(maxsize=None)
def combined(a,b):
    return max(x+y+dim(S&T) for S,x in zip(SUBS,a) for T,y in zip(SUBS,b))


def plane_flats(n):
    ans = []
    for m in range(1,1 << n):
        ans.append((1 | 1 << m, (m,)))
    planes = {}
    for a,b in combinations(range(1,1 << n),2):
        planes[1 | 1 << a | 1 << b | 1 << (a^b)] = (a,b)
    ans.extend(planes.items())
    out = []
    for space, rows in ans:
        for offsets in range(1 << len(rows)):
            forbidden = sum(1 << x for x in range(1 << n)
                            if all((x & r).bit_count()%2 == (offsets >> i & 1)
                                   for i,r in enumerate(rows)))
            out.append((space,forbidden))
    return out


def projection(valid):
    F = 0
    for x in members(valid):
        F |= 1 << (x & 3)
    return F


def summarize(n, clauses):
    good = (1 << (1 << n))-1
    for _, forbidden in clauses:
        good &= ~forbidden
    return profile(tuple(sorted(space for space,_ in clauses))),projection(good)


def exact(F):
    if F == FULL:
        return profile(())
    if F.bit_count() == 3:
        return profile((K,))
    if F.bit_count() == 2:
        return profile((next(l for l in LINES if F in HALF[l]),))
    if F.bit_count() == 1:
        return profile((LINES[0],LINES[1]))
    raise AssertionError("an empty child rejects directly")


def verify(c,d):
    cp,F = c
    dp,E = d
    orig = combined(cp,dp)
    if orig > 1:
        return None
    dc,dd = budget(cp,K),budget(dp,K)
    assert dc+dd <= orig+2
    solved = bool(F&E)
    if not F:
        return 'empty'
    summary = exact(F)
    assert all(budget(summary,L) <= budget(cp,L) for L in SUBS)
    if dc <= 1:
        assert combined(summary,dp) <= orig
        return 'exact'
    if dc == 3:
        assert dd == 0 and E == FULL and solved
        return 'outside-full'
    assert dc == 2 and dd <= 1 and (not E or E.bit_count() >= 2)
    safe = [l for l in LINES if budget(cp,l) <= 1]
    assert len(safe) >= 2
    fixed = [half for l in safe for half in HALF[l] if not (F & ~half)]
    if fixed:
        prediction = FULL
        for half in fixed:
            prediction &= half
        assert prediction == F
        assert combined(summary,dp) <= orig
        return 'singleton' if len(fixed)>1 else 'line'
    assert solved == bool(E)
    if len(safe) == 2:
        unsafe = next(l for l in LINES if l not in safe)
        assert budget(dp,unsafe) == 0 and all(E & half for half in HALF[unsafe])
    assert combined(profile(()),dp) <= orig
    return 'drop-' + str(F.bit_count())


def census(n, limit):
    flats = plane_flats(n)
    groups = Counter()
    for m in range(limit+1):
        for clauses in combinations_with_replacement(flats,m):
            sig = summarize(n,clauses)
            if budget(sig[0],1) <= 1:
                groups[sig] += 1
    return groups


def pair_census(groups):
    counts = Counter()
    for c,cm in groups.items():
        for d,dm in groups.items():
            mode = verify(c,d)
            if mode is not None:
                counts[mode] += cm*dm
    return counts


def direct(nc,nd,C,D):
    # Independently rebuild actual full normal spaces in the glued variables;
    # the two private parts occupy disjoint bit positions.
    def remap(v):
        return (v & 3) | ((v & ~3) << (nc-2))
    spaces = [s for s,_ in C]+[sum(1 << remap(v) for v in members(s)) for s,_ in D]
    best = 0
    for mask in range(1 << len(spaces)):
        rows = {}
        for i,s in enumerate(spaces):
            if mask >> i & 1:
                for r in members(s):
                    while r and r.bit_length() in rows:
                        r ^= rows[r.bit_length()]
                    if r:
                        rows[r.bit_length()] = r
        best = max(best,mask.bit_count()-len(rows))
    feasible = any(all(not(f >> (x & ((1 << nc)-1)) & 1) for _,f in C) and
                   all(not(f >> ((x & 3) | ((x >> nc) << 2)) & 1) for _,f in D)
                   for x in range(1 << (nc+nd-2)))
    return best,feasible


if __name__ == '__main__':
    for n,limit in ((2,3),(3,4)):
        groups = census(n,limit)
        counts = pair_census(groups)
        print(n, 'coordinates per side;',sum(groups.values()),'side systems;',
              len(groups),'signatures;',sum(counts.values()),'admitted ordered gluings;',dict(counts),flush=True)
    rng = Random(20261204)
    small = {n:plane_flats(n) for n in (3,4)}
    admitted = 0
    for _ in range(900):
        nc,nd=rng.choices((3,4),k=2)
        C=rng.choices(small[nc],k=rng.randrange(5))
        D=rng.choices(small[nd],k=rng.randrange(5))
        c,d = summarize(nc,C),summarize(nd,D)
        measured,feasible = direct(nc,nd,C,D)
        assert measured == combined(c[0],d[0])
        assert feasible == bool(c[1]&d[1])
        if verify(c,d) is not None:
            admitted += 1
    print('900 independent direct gluings;',admitted,'admitted.')
