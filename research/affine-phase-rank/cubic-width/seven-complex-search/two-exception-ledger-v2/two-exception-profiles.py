"""Enumerate Bell/GHZ resource profiles on three labeled three-qubit parties."""
import csv
from collections import Counter
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path

PARTIES = tuple(range(3))
PERMS = list(permutations(PARTIES))
# First three entries count Bell pairs opposite A, B and C, respectively.
profiles = []
for a, b, c, g in product(range(4), repeat=4):
    if max(b + c, a + c, a + b) + g <= 3 and a + b + c + g > 0:
        profiles.append((a, b, c, g))


def relabel(profile, perm):
    return tuple(profile[i] for i in perm) + (profile[3],)


def pair_images(pair, ordered):
    result = set()
    for perm in PERMS:
        image = tuple(relabel(p, perm) for p in pair)
        result.add(image if ordered else tuple(sorted(image)))
    return result


def category(profile):
    links = sum(bool(k) for k in profile[:3])
    if profile[3] == 0 and links == 1:
        return 'B'
    if profile == (0, 0, 0, 1):
        return 'H'
    return 'T'


def verdict(pair):
    p, q = pair
    if category(p) == category(q) == 'B' and all(bool(x) == bool(y) for x, y in zip(p[:3], q[:3])):
        return 'excluded-common-cut'
    if category(p) == category(q) == 'H':
        return 'excluded-single-GHZ-pair'
    if {category(p), category(q)} == {'H', 'B'} and sum(p) == sum(q) == 1:
        return 'excluded-single-GHZ-and-single-Bell'
    if category(p) == category(q) == 'B' and sum(p) == sum(q) == 1 and p != q:
        return 'excluded-different-single-Bells'
    for i in PARTIES:
        left = p[3] + sum(p[:3]) - p[i]
        right = q[3] + sum(q[:3]) - q[i]
        if max(left, right) == 3 and min(left, right) <= 1:
            return 'excluded-Schmidt-support'
    return 'unresolved-by-listed-exclusions'


def code(p):
    return ''.join(map(str, p))


pairs = list(combinations_with_replacement(profiles, 2))
seen = set()
rows = []
for pair in pairs:
    if pair in seen:
        continue
    images = pair_images(pair, False)
    seen.update(images)
    assert pair == min(images)
    rows.append((code(pair[0]), code(pair[1]), len(images), verdict(pair)))
with Path(__file__).with_name('two-exception-profiles.csv').open('w') as fp:
    writer = csv.writer(fp, lineterminator='\n')
    writer.writerow(('first_profile', 'second_profile', 'labeled_unordered_pair_count', 'status'))
    writer.writerows(rows)
print('profiles by GHZ number', sorted(Counter(p[3] for p in profiles).items()))
print('single profiles labeled, unlabeled:', len(profiles), len({min(relabel(p, t) for t in PERMS) for p in profiles}))
print('ordered pairs labeled, unlabeled:', len(profiles)**2, len({min(pair_images((p,q), True)) for p in profiles for q in profiles}))
print('unordered pairs labeled, unlabeled:', len(pairs), len(rows))
print('labeled unordered by verdict:', sorted(Counter(map(verdict, pairs)).items()))
print('unlabeled unordered by verdict:', sorted(Counter(row[3] for row in rows).items()))
print('labeled unordered by class:', sorted(Counter(''.join(sorted(map(category, pair))) for pair in pairs).items()))
print('unlabeled unordered by class:', sorted(Counter(''.join(sorted((category(p), category(q)))) for p,q in pairs if (p,q)==min(pair_images((p,q),False))).items()))
