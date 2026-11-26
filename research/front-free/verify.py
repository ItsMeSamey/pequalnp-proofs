"""Check the front-free raw suffix against the pinned raw-child statement."""
import argparse
import sys
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path, help='folder containing verify_packing.py and L-meta-18968.json')
args = parser.parse_args()
sys.path.insert(0, str(args.source.resolve()))
from verify_packing import samples, require

rows, front, target = samples(args.source / 'L-meta-18968.json')
live = (1 << 38)-1
positive = {row & live for k, row in enumerate(rows) if (target ^ front) >> k & 1}
negative = {row & live for k, row in enumerate(rows) if not target >> k & 1}
maximal = {n for n in negative if not any(n != m and not n & ~m for m in negative)}
require(len(positive) == 28 and len(maximal) == 245, 'unexpected residual matrix')
for p in positive:
    q = (p & 8191).bit_length()-1
    require((p & 8191).bit_count() == 1 and ((p >> 13) & 127).bit_count() == 1,
            'positive must have one raw point and one suffix line')
    if q != 1:
        require(any(p & ~n == 1 << q for n in maximal), 'missing raw point witness')
for line in range(13,20):
    witnesses = [n for p in positive for n in maximal if p & ~n == 1 << line]
    for j in range(20):
        if j != line:
            require(any(n >> j & 1 for n in witnesses), 'missing earliest-line witness')

features = [sum(1 << ((j+d)%13) for d in offsets)
            for offsets in ((0,1),(3,9),(0,1,3,9)) for j in range(6)]
for row in positive | maximal:
    encoded = sum(bool((row & 8191) & support) << i for i, support in enumerate(features))
    require(encoded == row >> 20, 'unexpected point feature')

six = tuple(range(7,13))
require(all((f & sum(1 << q for q in six)).bit_count() <= 1 for f in features),
        'supplied feature does not collapse')
deleted = {q for q in range(13) if q not in six and q != 1}
require(deleted == {0,2,3,4,5,6}, 'unexpected deleted coordinates')

point_one = 152474746882
negative_one = 169859090180
special_cut = (1 << 1) | (1 << 20)
require(point_one in positive and negative_one in maximal, 'missing point-1 witness')
require(point_one & ~negative_one == special_cut, 'unexpected point-1 cut')
require(point_one & 8191 == 2, 'witness is not a point-1 positive')
require(not point_one & sum(1 << q for q in deleted), 'previous deletion affects witness')
require(not any(p & special_cut for p in positive if p & sum(1 << q for q in six)),
        'point-1 cut is nonzero at a high point')
print('Seven paid point deletions: six private literals and the disjoint cut {1,20}.', flush=True)

mask = sum(1 << q for q in six)
high = [p for p in positive if p & mask]
zero = [i for i in range(38) if all(not p >> i & 1 for p in high)]
require(len(zero) == 13, 'unexpected vanishing set')
forced = {q for q in deleted}
for q in forced:
    require(any(p & ~n == 1 << q for p in positive for n in maximal), 'missing required literal')
for j in (20,21):
    require(j in zero and any(p & ~n == (2 | (1<<j)) for p in positive for n in maximal),
            'missing alternative erasure charge')
print('Vanishing primitive coordinates:', zero)
print('Six required literal uses and one additional use, or two when raw point 1 is absent.')

# samples() stores the live 38 coordinates first, followed by the six front
# line coordinates and w54. Rebuild the raw indices 0..43 in published order.
raw = [(r & 8191) | (((r >> 38) & 63) << 13) | (((r >> 13) & ((1 << 25)-1)) << 19)
       for r in rows]
pairs = [(0,52),(1,52),(2,52),(3,53),(4,54),(5,55)]
for j,(p,n) in enumerate(pairs,13):
    require((target >> p) & 1 and not (target >> n) & 1, 'unexpected private-line labels')
    require(raw[p] & ~raw[n] == 1 << j, 'missing raw front-line witness')
high_positions = [k for k,r in enumerate(rows) if ((target ^ front) >> k & 1)
                  and (r & sum(1 << q for q in range(7,13)))]
vanish = [i for i in range(44) if all(not (raw[k] >> i & 1) for k in high_positions)]
require(vanish == [*range(7),*range(13,19),*range(26,32)], 'unexpected raw vanishing coordinates')
print('Front-free singleton line witnesses:',pairs)
print('Original raw wires vanishing on the high-point positives:', vanish)
print('34 gates force exactly one use of each w0..6 and w13..18, and zero uses of w26..31.')
available = [*range(26), *range(32,44)]
reduced = [row & sum(1 << i for i in available) for row in raw]
pos_reduced = {r for k,r in enumerate(reduced) if (target >> k) & 1}
neg_reduced = {r for k,r in enumerate(reduced) if not (target >> k) & 1}
forced = [*range(7), *range(13,19)]
erased = sum(1 << i for i in forced)
allowed = {}
for i in forced:
    priv = [(p,n) for p in pos_reduced for n in neg_reduced if p & ~n == 1 << i]
    require(any(p & erased == 1 << i for p,n in priv),
            'erasing the other twelve could destroy this private witness')
    occurs = 0
    for p,n in priv:
        occurs |= n
    allowed[i] = {j for j in available if j != i and not occurs & (1 << j)}
for idx,i in enumerate(forced):
    for j in forced[idx+1:]:
        require(j not in allowed[i] or i not in allowed[j],
                'two forced wires might pass through the same OR')
require(all(not allowed[i] for i in range(13,19)), 'front raw line allows a primitive partner')
require(not (allowed[2] - set(forced)), 'raw point 2 allows an unforced primitive partner')
print('All 13 unique uses enter distinct OR gates. Each front-line partner must be mixed.')

def high_projection(raw_row):
    return ((raw_row >> 7) & 63) | (((raw_row >> 19) & 127) << 6)

high_neg = {high_projection(n) for n in neg_reduced}
high_max = {n for n in high_neg if not any(n != m and not n & ~m for m in high_neg)}
require(len(high_max) == 33, 'unexpected high-point negative family')
expected = [122,1063,1063,4125,122,4125]
for i,exception in enumerate(expected,13):
    private = {high_projection(n) for p in pos_reduced for n in neg_reduced if p & ~n == 1 << i}
    missing = {n for n in high_max if not any(not n & ~m for m in private)}
    require(missing == {exception}, 'unexpected uncovered high negative')
print('Uncovered high-core negative masks for front lines 13..18:', expected)
