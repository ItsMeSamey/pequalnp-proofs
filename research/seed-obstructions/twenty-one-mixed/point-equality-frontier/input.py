from hashlib import sha256
import json
import re

def raw_samples(path):
    statement = json.loads(path.read_text())['formal_statement']
    assert sha256(statement.encode()).hexdigest() == 'd5fbefe3ea85033034056aae8ed0b90ecfe428b8a69e3456176309d0c82b54c2'
    blocks = re.findall(r'\[((?:\(\d+ : ℕ\)(?:, )?)+)\]', statement)
    assert len(blocks) == 2
    columns = []
    for block in blocks:
        seed = 0
        for part in re.findall(r'\((\d+) : ℕ\)', block):
            seed = seed * 10**19 + int(part)
        for shift in range(13):
            col = 0
            for start in range(0, 676, 13):
                lane = (seed >> start) & 8191
                col |= (((lane << shift) | (lane >> (13-shift))) & 8191) << start
            columns.append(col)
    front, target = [int(re.search(r'x1 \(' + str(j) + r' : ℕ\) = \((\d+) : ℕ\)', statement)[1])
                     for j in (54, 88)]
    relevant = columns[:13] + columns[19:26]
    rows = [sum(((col >> i) & 1) << j for j,col in enumerate(relevant)) for i in range(676)]
    pos = {r for i,r in enumerate(rows) if (target ^ front) >> i & 1}
    neg = {r for i,r in enumerate(rows) if not target >> i & 1}
    all_neg = set(neg)
    neg = {r for r in neg if all(r == s or r & ~s for s in neg)}
    assert len(pos) == 28 and len(neg) == 245
    return pos, neg, all_neg


def point_obligations(path):
    positives, negatives, _ = raw_samples(path)
    neighbors = {1 << j: set() for j in range(13)}
    for positive in positives:
        point = positive & 8191
        assert point in neighbors
        for negative in negatives:
            if not ((positive >> 13) & ~(negative >> 13)):
                neighbors[point].add(negative & 8191)
    rows = sorted((point, mask) for point, masks in neighbors.items() for mask in masks
                  if not any(mask != other and not (mask & ~other) for other in masks))
    assert len(rows) == 1323
    raw = {1 << j for j in range(13)}
    for j in range(6):
        first_pair = (1 << j) | (1 << (j + 1))
        second_pair = (1 << (j + 3)) | (1 << ((j + 9) % 13))
        raw.update((first_pair, second_pair, first_pair | second_pair))
    assert len(raw) == 31
    return sorted(raw), rows
