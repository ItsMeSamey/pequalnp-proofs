"""Small direct color and pinned-bucket oracle checks."""
from collections import Counter
from itertools import product
from random import Random
from isolation_check import directed_tours


def check(rows, rng):
    tours, ids = directed_tours(rows)
    weights = [rng.randrange(3) for _ in ids]
    covers = []
    for p in product(*rows):
        if len(set(p)) == len(rows):
            mask = sum(1 << ids[i, j] for i, j in enumerate(p))
            weight = sum(weights[i] for i in range(len(ids)) if mask >> i & 1)
            covers.append((p,mask,weight))
    def color_counts(palette):
        count = Counter()
        for tail in product(range(palette),repeat=len(rows)-1):
            colors = (0,) + tail
            for p,mask,weight in covers:
                if all(colors[i] == colors[j] for i,j in enumerate(p)):
                    count[mask,weight] += 1
        return count
    binary = color_counts(2)
    def odd(s,zero,one):
        return sum(n for (m,w),n in binary.items() if w==s and not m&zero and m&one==one)%2
    buckets = queries = 0
    for s in set(w for m,w in binary):
        if not odd(s,0,0):
            continue
        zero = one = 0
        for j in range(len(ids)):
            bit = 1 << j
            if odd(s,zero | bit,one):
                zero |= bit
            else:
                one |= bit
            queries += 1
        assert tuple(i for i in range(len(ids)) if one>>i&1) in tours
        assert sum(weights[i] for i in range(len(ids)) if one>>i&1)==s
        buckets += 1
    residues = [sum(binary.values())%2, sum(color_counts(3).values())%3]
    assert len(tours)<6
    assert [v for v in range(6) if [v%2,v%3]==residues] == [len(tours)]
    return buckets, queries


rng=Random(711)
buckets=queries=0
for n in range(1,7):
    for i in range(32):
        a,b=list(range(n)),list(range(n))
        rng.shuffle(a)
        rng.shuffle(b)
        rows=[tuple(sorted({x,y})) for x,y in zip(a,b)]
        b,q=check(rows,rng)
        buckets+=b
        queries+=q
print(f'192 CRT reconstructions, {buckets} odd buckets, {queries} pin queries')
