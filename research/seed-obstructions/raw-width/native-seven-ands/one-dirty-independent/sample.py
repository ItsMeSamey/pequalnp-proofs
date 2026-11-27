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


