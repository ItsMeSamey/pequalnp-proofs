from pathlib import Path
from itertools import combinations
from verify_packing import samples
rows, _, target = samples(Path(__file__).with_name("L-meta-18968.json"))
pos = [r for i,r in enumerate(rows) if target >> i & 1]
neg = [r for i,r in enumerate(rows) if not target >> i & 1]
stars = [sum({r & 8191 for r in pos if r >> (13+j) & 1}) for j in range(7)]
assert all(star.bit_count() == 4 for star in stars)
for a,b in combinations(range(13),2):
    x=(1<<a)|(1<<b)
    assert all(any(n & x == x and n & star for n in neg) for star in stars)
print("All 78 point pairs extend to negatives meeting each of seven prescribed neighborhoods.")
for t,u,v in ((t,u,v) for t in range(7) for u in range(7) for v in range(7) if len({t,u,v})==3):
    exclusive = [i for i in range(13) if stars[t] >> i & 1 and not stars[u] >> i & 1]
    exterior = [i for i in range(13) if not stars[u] >> i & 1]
    for a,b in combinations(exterior,2):
        x=(1<<a)|(1<<b)|(1<<(13+u))
        for q,r in combinations(exclusive,2):
            assert any(n & x == x and n & ((1<<q)|(1<<r)) and n & stars[v] for n in neg)
print("All two-exclusive-point extensions with an extra ordinary neighborhood hold.")
