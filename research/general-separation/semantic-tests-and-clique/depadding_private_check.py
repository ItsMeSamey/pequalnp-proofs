"""Private heavy-variable expansion of signed sums for all small embeddings."""
from itertools import product
from random import Random

rng = Random(182)
cases = 0
for _ in range(50):
    atoms = [[rng.randrange(6) for _ in range(12)] for _ in range(4)]
    weights = [rng.randrange(-4,5) for _ in atoms]
    def compute(leaves, raw):
        value = 0
        for i,pos in enumerate(leaves):
            value = (value ^ raw[pos]) if i%2 else (value | raw[pos])
        return value
    for choices in product(range(2),repeat=3):
        selected = [2*j+s for j,s in enumerate(choices)]
        heavy = [[j for j,s in enumerate(selected) if a.count(s)>2] for a in atoms]
        for x in product(range(2),repeat=3):
            raw = [0]*6
            for j,s in enumerate(selected):
                raw[s]=x[j]
            total = sum(w*compute(a,raw) for w,a in zip(weights,atoms))
            split = 0
            for w,a,h in zip(weights,atoms,heavy):
                for b in product(range(2),repeat=len(h)):
                    pinned = raw.copy()
                    for j,v in zip(h,b):
                        pinned[selected[j]]=v
                    split += w*compute(a,pinned)*all(x[j]==v for j,v in zip(h,b))
            assert total==split
            cases += 1
print(cases,'signed private expansion checks passed')
