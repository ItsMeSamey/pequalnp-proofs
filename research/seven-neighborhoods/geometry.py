from itertools import combinations,permutations
L=[{(i+d)%13 for d in (0,1,3,9)} for i in range(7)]
def fingerprint(ids):
 return min(tuple(sorted(sum(1<<j for j,t in enumerate(p) if x in L[t]) for x in range(13))) for p in permutations(ids))
for m,representatives in [(4,[(0,1,2,3),(0,1,2,4)]),(6,[(0,1,2,3,4,5),(0,1,2,3,4,6)])]:
 assert {fingerprint(s) for s in combinations(range(7),m)}=={fingerprint(s) for s in representatives}
pencils=[set(c) for c in combinations(range(7),3) if set.intersection(*(L[t] for t in c))]
assert len(pencils)==6 and all(a&b for a,b in combinations(pencils,2))
print('Checked four- and six-line orbit coverage, six pairwise-intersecting pencils.')
