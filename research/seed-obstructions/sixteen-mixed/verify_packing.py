"""Check fixed-prefix obstructions against L-meta-18968 using only Python."""
import argparse
import hashlib
import json
import re
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)

def samples(source):
    statement = json.loads(source.read_text())['formal_statement']
    require(hashlib.sha256(statement.encode()).hexdigest() ==
            'd5fbefe3ea85033034056aae8ed0b90ecfe428b8a69e3456176309d0c82b54c2',
            'unexpected formal statement')
    blocks = re.findall(r'\[((?:\(\d+ : ℕ\)(?:, )?)+)\]', statement)
    require(len(blocks) == 2, 'expected two decimal seed blocks')
    columns = []
    for block in blocks:
        seed = 0
        for chunk in re.findall(r'\((\d+) : ℕ\)', block):
            seed = seed * 10**19 + int(chunk)
        for shift in range(13):
            value = 0
            for pos in range(0, 676, 13):
                lane = (seed >> pos) & 8191
                rotated = ((lane << shift) | (lane >> (13-shift))) & 8191
                value |= rotated << pos
            columns.append(value)
    for j in range(6):
        columns.append(columns[j] | columns[j+1])
    for j in range(6):
        columns.append(columns[j+3] | columns[(j+9)%13])
    for j in range(6):
        columns.append(columns[26+j] | columns[32+j])
    front, target = [int(re.search(r'x1 \(' + str(index) +
                                  r' : ℕ\) = \((\d+) : ℕ\)', statement)[1])
                     for index in (54, 88)]
    # Place retained primitives first, then the seven other readable wires.
    wires = columns[:13] + columns[19:44] + columns[13:19] + [front]
    rows = [sum(((col >> i) & 1) << j for j,col in enumerate(wires))
            for i in range(676)]
    return rows, front, target

def verify(file, rows, front, target):
    proof = json.loads(file.read_text())
    seed = proof['seed']
    fixed = proof['fixed'] if 'fixed' in proof else list(range(proof['prefix']))
    require(fixed == sorted(set(fixed)) and all(0 <= i < len(seed) <= 34 for i in fixed),
            'invalid fixed gate slots')
    k = len(fixed)
    available = set(range(38))
    for slot in fixed:
        op,a,b = seed[slot]
        require(op in ('and','or') and a in available and b in available,
                'invalid or nonclosed gate set')
        available.add(38+slot)
    def evaluate(raw):
        row = raw & ((1 << 38)-1)
        for slot in fixed:
            op,a,b = seed[slot]
            x,y = (row >> a) & 1,(row >> b) & 1
            row |= (x & y if op == 'and' else x | y) << (38+slot)
        return row | ((raw >> 38) << (38+len(seed)))
    positive, negative, erased = {}, {}, {}
    mask = (1 << 38)-1
    require(not front & ~target, 'front-positive outside target')
    for i,row in enumerate(rows):
        table = erased if (front >> i)&1 else positive if (target >> i)&1 else negative
        table.setdefault(row & mask, i)
        if table is positive:
            require(row >> 38 == 0, 'omitted positive input')
    require(all(any(p & ~n == 0 for n in negative) for p in erased),
            'undominated erased positive')
    used = 0
    def add(i,j):
        nonlocal used
        require((target >> i)&1 and not (target >> j)&1, 'incorrect target labels')
        delta = evaluate(rows[i]) & ~evaluate(rows[j])
        require(delta and not delta & used, 'empty or overlapping support differences')
        used |= delta
    for p,n in proof['pairs']:
        add(positive[p],negative[n])
    i,j = next((i,j) for p,i in erased.items() for n,j in negative.items() if p & ~n == 0)
    add(i,j)
    count = len(proof['pairs']) + 1
    require(count-1 > 34-k, 'packing fails to exclude completion')
    print(f'{file.name}: extra raw pair ({i}, {j}), {count} disjoint supports, '
          f'{count-1} gates required, {34-k} available')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('certificates', nargs='+', type=Path)
    args = parser.parse_args()
    data = samples(args.source)
    for cert in args.certificates:
        verify(cert,*data)
