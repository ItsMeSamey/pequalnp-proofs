"""Verify the complete lower-bound histogram and retain candidate families."""
import sys
from collections import Counter

expected = {12:23, 13:237, 14:2097, 15:11889, 16:70584, 17:219954,
            18:640534, 19:169416, 20:103536}
counts = Counter()
with open(sys.argv[1],'w') as low:
    for row in sys.stdin:
        data = tuple(map(int,row.split()))
        if len(data)!=11:
            raise ValueError('expected ten masks and one bound')
        counts[data[-1]] += 1
        if data[-1]<=16:
            low.write(row)
if counts != expected:
    raise ValueError(counts)
print('Point-gate lower bound and number of irreducible families')
for k in sorted(counts):
    print(k,counts[k])
