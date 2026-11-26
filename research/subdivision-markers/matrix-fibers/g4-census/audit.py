"""Separate full-span audit, with direct enumeration of conjugating matrices."""
from collections import Counter

I = 0x8421

def act(a,x):
    return sum((((a >> (4*i)) & x).bit_count() & 1) << i for i in range(4))

def mat(images):
    return sum(((y >> i) & 1) << (4*i+j) for j,y in enumerate(images) for i in range(4))

def compose(a,b):
    return mat([act(a,act(b,1<<j)) for j in range(4)])

def main():
    inv = {}
    action = {}
    for a in range(65536):
        columns = [sum(((a>>(4*i+j))&1)<<i for i in range(4)) for j in range(4)]
        images = [0]
        for x in columns:
            images += [x^y for y in images]
        if len(set(images)) == 16:
            action[a] = images
            inv[a] = mat([images.index(1<<j) for j in range(4)])
    phi = {a^I:v^I for a,v in inv.items()}
    column_mask = [[mat([v if i==j else 0 for i in range(4)]) for v in range(16)] for j in range(4)]
    reps = (2,19,20,72,310,311,314,315,4698,4699,4700,4701,4713)
    visited = set()
    counts = Counter()
    weighted = Counter()
    for a in reps:
        # Conjugation by *every* invertible matrix, independently of generators.
        orbit = set()
        acts = [act(a,j) for j in range(16)]
        for g,h in inv.items():
            p, q = action[g], action[h]
            orbit.add(sum(column_mask[j][p[acts[q[1 << j]]]] for j in range(4)))
        assert orbit <= phi.keys() and not orbit & visited
        visited |= orbit
        candidates = [v for v in phi if v not in (0,a)
                      and phi.get(v ^ a) == phi[v] ^ phi[a]]
        layer = {frozenset([0,a])}
        d = 1
        while layer:
            if d==4:
                assert all(compose(x,y)==0 for L in layer for x in L for y in L)
                print('extremizers through',a,':',len(layer),flush=True)
            counts[d] += len(layer)
            weighted[d] += len(orbit) * len(layer)
            nxt = set()
            for L in layer:
                for v in candidates:
                    if v in L:
                        continue
                    # Check the actual inverse for all elements of the whole new
                    # coset. Treat the full point set as the deduplication key.
                    if all(phi.get(u^v) == (phi[u]^phi[v]) for u in L):
                        nxt.add(L | {u^v for u in L})
            d += 1
            layer = nxt
    assert visited == phi.keys() - {0}
    assert dict(counts) == {1:13,2:221,3:88,4:4}
    for d, point in sorted(weighted.items()):
        num,rem = divmod(point,(1<<d)-1)
        assert rem == 0
        print(d, 'unmarked normalized spaces', num)
    print('All conjugations and full cosets verified.')

if __name__ == '__main__':
    main()
