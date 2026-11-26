"""Apply the projected-target and 21-gate equality bounds to low-cost families."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import sys

targets = [sum(1 << ((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
free = {1 << i for i in range(13)}
for j in range(6):
    a = (1<<j) | (1<<(j+1))
    b = (1<<(j+3)) | (1<<((j+9)%13))
    free.update([a,b,a|b])

def refine(family, completion_bound):
    paid = [m for m in family if m not in free]
    full = [t for t in targets if t in family]
    bound = completion_bound
    for n in range(1, min(5,len(full))+1):
        for selected in combinations(full,n):
            transversals = sum(all((m&t).bit_count()<=1 for t in selected) for m in paid)
            bound = max(bound,3*n+transversals)
    if bound != completion_bound:
        return bound
    if any(all(m&~t for t in targets) for m in paid):
        return bound+1
    for a,b in combinations(paid,2):
        overlap_without_containment = (a&b) and (a&~b) and (b&~a)
        if overlap_without_containment and any(not (a|b)&~t for t in targets):
            return bound+1
    return bound

def run(source, destination):
    histogram = Counter()
    with Path(source).open() as rows, Path(destination).open('w') as output:
        for row in rows:
            values = list(map(int,row.split()))
            if len(values)!=11:
                raise ValueError('expected ten masks and one bound')
            family,lower = values[:-1],values[-1]
            bound = refine(family,lower)
            histogram[bound] += 1
            if bound<=16:
                print(*family,bound,file=output)
    expected = {12:23,13:237,14:1245,15:5038,16:16731,17:52319,18:8744,19:469,20:24}
    if histogram != expected:
        raise ValueError(histogram)
    print('Refined low-budget histogram', dict(sorted(histogram.items())))

if __name__ == '__main__':
    run(*sys.argv[1:])
