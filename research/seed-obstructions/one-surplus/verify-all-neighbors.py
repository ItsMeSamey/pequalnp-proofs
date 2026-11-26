from pathlib import Path
from verify_packing import samples
rows, _, target = samples(Path(__file__).with_name("L-meta-18968.json"))
positive = [r for i,r in enumerate(rows) if target >> i & 1]
negative = [r for i,r in enumerate(rows) if not target >> i & 1]
stars = [sum({r & 8191 for r in positive if r >> (13+t) & 1}) for t in range(7)]
assert all(s.bit_count() == 4 for s in stars)
checked = 0
for t,star in enumerate(stars):
    for p in range(13):
        if star >> p & 1:
            continue
        required = (1 << (13+t)) | (1 << p)
        assert any(n & required == required and all(n & s for u,s in enumerate(stars) if u != t) for n in negative)
        checked += 1
assert checked == 63
print(checked, "exterior singleton and six-neighborhood extensions")
