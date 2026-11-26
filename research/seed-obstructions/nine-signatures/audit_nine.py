"""Check each emitted nine-mask family directly against the maximal sample obligations."""
from functools import lru_cache
from inputs import base, canonical, maximal

@lru_cache(maxsize=None)
def covers(mask):
    return sum(1 << i for i,(p,n) in enumerate(maximal) if mask & p and not mask & n)

def read(name):
    return [tuple(map(int,row.split())) for row in (base/name).read_text().splitlines()]

families = read('nine.txt')
eight = set(read('families.txt'))
full = (1 << len(maximal))-1
if len(families) != 16924 or families != sorted(set(families)):
    raise ValueError('unexpected number or ordering of nine-mask families')
for family in families:
    if len(family) != 9 or family != tuple(sorted(family)) or max(family) > 8191 or min(family) < 0:
        raise ValueError(('bad family', family))
    if set(canonical) <= set(family) or any(family[:i] + family[i+1:] in eight for i in range(9)):
        raise ValueError(('contains a smaller base', family))
    covered = 0
    for mask in family:
        covered |= covers(mask)
    if covered != full:
        raise ValueError(('violated obligation', family))
print(f'All {len(families)} nine-mask families are irreducible and satisfy every obligation.')
