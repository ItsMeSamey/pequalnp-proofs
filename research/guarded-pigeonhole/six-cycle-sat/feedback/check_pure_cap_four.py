"""Enumerate all maximal singular caps for four classes in binary split space."""
from itertools import combinations, permutations


def rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            j = v.bit_length()
            if j not in basis:
                basis[j] = v
                break
            v ^= basis[j]
    return len(basis)


def subspaces(n):
    for r in range(n+1):
        for pivots in combinations(range(n),r):
            free = [(i,j) for i,p in enumerate(pivots) for j in range(p+1,n) if j not in pivots]
            for mask in range(1<<len(free)):
                rows = [1<<j for j in pivots]
                for h,(i,j) in enumerate(free):
                    if mask>>h & 1:
                        rows[i] ^= 1<<j
                yield pivots,rows


def cap_bases(n):
    for pivots,rows in subspaces(n):
        r = len(rows)
        annihilator = []
        for j in range(n):
            if j not in pivots:
                v = 1<<j
                for p,row in zip(pivots,rows):
                    if row>>j & 1:
                        v |= 1<<p
                annihilator.append(v<<n)
        pairs = list(combinations(range(r),2))
        for mask in range(1<<len(pairs)):
            cov = [0]*r
            for k,(i,j) in enumerate(pairs):
                if mask>>k & 1:
                    cov[i] ^= 1<<pivots[j]
                    cov[j] ^= 1<<pivots[i]
            yield [y ^ (z<<n) for y,z in zip(rows,cov)] + annihilator


def signature(cycles,n):
    sigma = list(range(n+1))
    for cycle in cycles:
        for i,j in zip(cycle,cycle[1:]+cycle[:1]):
            sigma[i] = j
    rows = []
    for i in range(n):
        y = (1<<i) ^ (1<<sigma[i])
        z = (1<<i)
        for j in range(n+1):
            z ^= ((y>>(j+1)).bit_count()%2)<<j
        if z>>n & 1:
            z ^= (1<<(n+1))-1
        rows.append((y & ((1<<n)-1)) ^ (z<<n))
    return rows


if __name__ == '__main__':
    n = 5
    a,b = 1,4
    classes = [0,2,3,5]
    splits = [signature(((a,i),(b,j)),n) for i,j in permutations(classes,2)]
    joined = [signature((cycle,),n) for i in classes for cycle in ((a,b,i),(b,a,i))]
    count = both = 0
    for cap in cap_bases(n):
        count += 1
        if all(rank(cap+sig) == 2*n for sig in splits):
            assert all(rank(cap+sig) == 2*n for sig in joined)
            both += 1
    print(f'{count} caps; all {both} universally split-transverse caps also accept every join')
