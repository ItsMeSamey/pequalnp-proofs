"""Six permutation orbits of 5-by-5 binary matrices with even margins and rank 4."""
from itertools import permutations, product, combinations


def span(basis):
    words = [0]
    for x in basis:
        words += [y ^ x for y in words]
    return words


def orbit_reps():
    even = [i for i in range(32) if i.bit_count() % 2 == 0]
    seen = set()
    for a,b,c,d in product(even, repeat=4):
        rows = (a,b,c,d,a^b^c^d)
        if len(set(rows)) != 5 or 0 in rows or tuple(sorted(rows)) in seen:
            continue
        for p in permutations(range(5)):
            seen.add(tuple(sorted(sum(((x>>j)&1)<<i for i,j in enumerate(p)) for x in rows)))
        yield rows


def quotient(rows):
    R = [x|32 for x in rows] + [31]
    S = set()
    for x,y in product(range(64),repeat=2):
        if any((x>>i)&1 and (t&y).bit_count()%2 for i,t in enumerate(R)):
            continue
        d = 0
        for i,t in enumerate(R):
            if (x>>i)&1:
                d ^= t
        if d&y:
            continue
        z = (x|(y<<6)) ^ (32|(32<<6))
        S.add(min(z,z^4095))
    return S


def find_fourflat(S):
    cand = sorted(S-{0})
    def extend(basis,L):
        if len(basis)==4:
            return basis
        for x in cand:
            if basis and x<=basis[-1]:
                continue
            C = [x^t for t in L]
            if min(C)==x and all(t in S for t in C):
                out=extend(basis+[x],L+C)
                if out:
                    return out
        return None
    return extend([],[0])


caps = {(3,5,10,20,24): ([99,165,1830,298,532], [10,13,16,18,19,20,21,23,27,28]),
        (3,5,10,23,27): ([114,172,1854,303,552], [11,12,16,17,18,21,22,23,24,31])}
reps = list(orbit_reps())
assert len(reps)==6
for N in reps:
    S=quotient(N)
    basis=find_fourflat(S)
    if N in caps:
        assert not basis
        B,holes=caps[N]
        L=span(B)
        assert len(set(L))==32
        assert [i for i in range(1,32) if L[i] not in S]==holes
        assert all((x^y) not in holes for x,y in combinations(holes,2))
    else:
        assert basis and set(span(basis))<=S
    print(N,len(S)-1,basis or 'sum-free complement on five-flat')
