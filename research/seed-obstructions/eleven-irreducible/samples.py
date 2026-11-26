"""Decode residual samples and compute their point-coordinate symmetries."""
from hashlib import sha256
from itertools import permutations
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
    neg = {r for r in neg if all(r == s or r & ~s for s in neg)}
    assert len(pos) == 28 and len(neg) == 245
    return pos, neg

def permute(mask, images):
    return sum(1 << v for j,v in enumerate(images) if mask >> j & 1)

def actions(pos, neg):
    stars = [sum(1 << ((6+j+d) % 13) for d in (0,1,3,9)) for j in range(7)]
    incidence = [sum(bool(s >> p & 1) << j for j,s in enumerate(stars)) for p in range(13)]
    assert len(set(incidence)) == 13
    group = []
    for lines in permutations(range(7)):
        moved = [permute(i,lines) for i in incidence]
        if set(moved) != set(incidence):
            continue
        points = [incidence.index(i) for i in moved]
        pm = [0]*8192
        for v in range(1,8192):
            bit = v & -v
            pm[v] = pm[v^bit] | (1 << points[bit.bit_length()-1])
        lm = [permute(v,lines) << 13 for v in range(128)]
        def move(r):
            return pm[r & 8191] | lm[r >> 13]
        if {move(r) for r in pos} == pos and {move(r) for r in neg} == neg:
            group.append(pm)
    assert len(group) == 24
    return group
