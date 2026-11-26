"""Generate the eight-mask bases and quotient them by verified raw-obligation symmetries."""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import sys

source = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).resolve().parent.parent / 'seed-obstructions'
sys.path.insert(0, str(source))
from verify_packing import require, samples

rows, front, target = samples(source / 'L-meta-18968.json')
positive = {(r & 8191, r >> 13 & 127) for i,r in enumerate(rows) if (target ^ front) >> i & 1}
negative = {(r & 8191, r >> 13 & 127) for i,r in enumerate(rows) if not target >> i & 1}
obligations = {(p,n) for p,l in positive for n,k in negative if not l & ~k}
stars = tuple(sum(1 << ((j+d)%13) for d in (0,1,3,9)) for j in range(6,13))
families = set()
for T in stars:
    proper = [m for m in range(1,T) if not m & ~T]
    for a,b in combinations(proper,2):
        if a | b == T:
            families.add(tuple(sorted(({*stars} - {T}) | {a,b})))
for i in range(13):
    single = 1 << i
    incident = [T for T in stars if T & single]
    for r in (2,3):
        for short in combinations(incident,r):
            families.add(tuple(sorted([single, *(T ^ single if T in short else T for T in stars)])))
require(len(families) == 202 and all(len(f) == 8 for f in families), 'unexpected base classification')
require(all(sum(T >> i & 1 for T in stars) <= 3 for i in range(13)), 'four concurrent targets')

def move(mask, permutation):
    return sum(1<<j for i,j in enumerate(permutation) if mask>>i & 1)

incidence = [sum(bool(T & (1<<i)) << j for j,T in enumerate(stars)) for i in range(13)]
require(len(set(incidence)) == 13, 'ambiguous point signatures')
symmetries = []
for lines in permutations(range(7)):
    images = [move(s,lines) for s in incidence]
    if set(images) != set(incidence):
        continue
    points = [incidence.index(s) for s in images]
    masks = [0] * 8192
    for m in range(1,8192):
        masks[m] = masks[m & (m-1)] | 1 << points[(m & -m).bit_length()-1]
    if {(masks[p],masks[n]) for p,n in obligations} == obligations:
        symmetries.append(masks)
reps = Counter(min(tuple(sorted(perm[m] for m in f)) for perm in symmetries) for f in families)
require((len(symmetries),len(reps)) == (24,23), 'unexpected symmetry profile')
for family,multiplicity in sorted(reps.items()):
    missing = set(stars) - set(family)
    extras = sorted(set(family)-set(stars),key=int.bit_count)
    print(len(missing),multiplicity)
    unique = {m: [] for m in family}
    for p,n in obligations:
        eligible = [m for m in family if m & p and not m & n]
        require(eligible, 'invalid basis')
        if len(eligible)==1:
            unique[eligible[0]].append((p,n))
    for T in stars:
        outputs = [T] if T in family else extras if len(missing)==1 else [T ^ extras[0]]
        tests = set()
        for m in outputs:
            for a,b in combinations([i for i in range(13) if not T >> i & 1],2):
                pair = (1<<a) | (1<<b)
                choices = [(p,n) for p,n in unique[m] if not pair & ~n]
                require(choices, 'no base witness for off-pair')
                difficult = frozenset((p,n) for p,n in choices if not any(
                    p==q and n!=v and not n & ~v for q,v in choices))
                tests.add(difficult)
        # Covering a larger witness set also covers every subset of it.
        minimal = [t for t in tests if not any(s < t for s in tests)]
        print(len(minimal))
        for t in minimal:
            print(len(t), *(x for row in sorted(t) for x in row))
