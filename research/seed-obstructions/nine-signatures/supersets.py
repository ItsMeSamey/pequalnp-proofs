"""Count failures of pair protection after adding one mask to an eight-mask family."""
from collections import Counter
from itertools import combinations
from inputs import base, canonical, obligations

def extensions(required, forbidden):
    if required & forbidden:
        return
    free = 8191 & ~(required | forbidden)
    subset = free
    while True:
        yield required | subset
        if not subset:
            break
        subset = (subset-1) & free

def vulnerable_targets(family):
    missing = set(canonical) - set(family)
    added = sorted(set(family)-set(canonical), key=int.bit_count)
    unique = {mask: [] for mask in family}
    for point, negative in obligations:
        witnesses = [m for m in family if m & point and not m & negative]
        if len(witnesses) == 1:
            unique[witnesses[0]].append((point, negative))
    affected = {}
    for j,target in enumerate(canonical):
        if target in family:
            outputs = [target]
        elif len(missing) == 1:
            outputs = added
        else:
            outputs = [target ^ added[0]]
        for mask in outputs:
            for x,y in combinations((i for i in range(13) if not target >> i & 1), 2):
                pair = (1 << x) | (1 << y)
                required = forbidden = 0
                for point,negative in unique[mask]:
                    if not pair & ~negative:
                        required |= point
                        forbidden |= negative
                if not required:
                    raise ValueError('missing raw pair witness in base family')
                for extra in extensions(required, forbidden):
                    affected[extra] = affected.get(extra, 0) | (1<<j)
    return affected

if __name__ == '__main__':
    histogram = Counter()
    for line in (base/'families.txt').read_text().splitlines():
        family = tuple(map(int,line.split()))
        removed = len(set(canonical)-set(family))
        affected = vulnerable_targets(family)
        histogram[removed,0] += 8192-len(affected)
        for targets in affected.values():
            histogram[removed,targets.bit_count()] += 1
    expected = {(1,0):1404170,(1,1):29430,(2,0):169962,(2,1):2070,
                (3,0):48552,(3,1):600}
    if histogram != expected:
        raise ValueError(histogram)
    print('Missing base targets, potentially unsafe targets, number of extensions')
    for (missing,unsafe),count in sorted(histogram.items()):
        print(missing,unsafe,count)
