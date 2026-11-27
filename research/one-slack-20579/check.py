"""Replay the frozen graph, control, observable relation and lower-bound witnesses."""
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re
import runpy

HERE = Path(__file__).resolve().parent
BANK = [42, 65, 83, 86, 90, 94, 95, 99, 101, 102, 107, 110, 115, 165, 186]
ROOTS = [213, 222, 225]
DELETED = {96, 111, 112, 116, 117, 169, 170, 171, 172, 187, 188, 189, 190, 213, 222, 225}
PINNED = {
    'control.lean': '08b07ebb1edfb826bb061afcc09558ae5d75a6d4d626e43c373c4d8e6855d731',
    'statement.txt': 'e233b9b26bab1a8856b41abefce91ad2660f5139effd3df1ad8e11582240f816',
}

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def read_pinned(name):
    data = (HERE / name).read_bytes()
    require(sha256(data).hexdigest() == PINNED[name], f'Pinned bytes changed in {name}')
    return data.decode('utf-8')

def cone(codes, roots, stop=frozenset()):
    seen = set()
    pending = list(roots)
    while pending:
        w = pending.pop()
        if w < 64 or w in seen or w in stop:
            continue
        seen.add(w)
        pending.extend(codes[w - 64][1:])
    return seen

def wires(codes, r, c):
    values = [i == r for i in range(32)] + [j == c for j in range(32)]
    for opcode, a, b in codes:
        values.append((values[a] and values[b]) if opcode == 0 else (values[a] or values[b]))
    return values

def main():
    statement = read_pinned('statement.txt')
    control = read_pinned('control.lean')
    rows = [int(s, 16) for s in re.findall(r'0x([0-9a-fA-F]+)', statement)]
    require(len(rows) == 32 and rows == [int(s, 16) for s in re.findall(r'0x([0-9a-fA-F]+)', control)],
            'Control and statement must encode the same 32 rows')
    entries = control.split('let codes : List (ℕ × ℕ × ℕ) := [', 1)[1].split(']', 1)[0]
    codes = [tuple(map(int, m)) for m in re.findall(r'\((\d+),(\d+),(\d+)\)', entries)]
    require(len(codes) == 180 and all(o in (0, 1) and 0 <= a < i and 0 <= b < i
            for i, (o, a, b) in enumerate(codes, 64)), 'Invalid control gate list')
    require('if o = 0 then .and else .or, [a,b]⟩), 243⟩' in control, 'Control decoding changed')
    boundary_outputs = {w for i, (_, a, b) in enumerate(codes, 64) if i not in DELETED
                        for w in (a, b) if w in DELETED}
    require(boundary_outputs == set(ROOTS), 'Deleted region must have exactly three exposed wires')
    require(not (cone(codes, BANK + [121]) & DELETED), 'A donor or marker depends on the cut')
    retained = cone(codes, [243, 121], stop=set(ROOTS))
    require(165 in retained, 'Donor 165 must remain reachable outside the cut')

    # The suffix is a binary OR tree over exactly the sixteen AND terms.
    frontier = list(range(213, 229))
    require(all(codes[i - 64][0] == 0 for i in frontier), 'Invalid terminal terms')
    leaves = []
    pending = [243]
    while pending:
        w = pending.pop()
        if w in frontier:
            leaves.append(w)
        else:
            require(w >= 229 and codes[w - 64][0] == 1, 'Invalid terminal disjunction')
            pending.extend(codes[w - 64][1:])
    require(sorted(leaves) == frontier, 'Unexpected term multiplicities')

    care = {}
    allowed = {}
    signature = 0
    for r, c in product(range(32), repeat=2):
        v = wires(codes, r, c)
        target = (rows[r] >> c) & 1
        require(v[243] == target, f'Control graph mismatch at {(r,c)}')
        if r == c < 6:
            signature |= int(not v[121]) << r
        outside = int(any(v[w] for w in frontier if w not in ROOTS))
        donor = sum(int(v[w]) << j for j, w in enumerate(BANK))
        care[r,c] = (donor, target, outside)
        permitted = {t for t in range(8) if int(bool(t) or outside) == target}
        allowed[donor] = allowed.get(donor, set(range(8))) & permitted
    require(signature == 53, 'The appended first internal NOT has the wrong mask')
    histogram = {n:sum(len(a) == n for a in allowed.values()) for n in (1, 7, 8)}
    require(len(allowed) == 171 and histogram == {1:96, 7:47, 8:28}, 'Joint care differs')
    positive = [p for p, a in allowed.items() if a == set(range(1, 8))]
    negative = [p for p, a in allowed.items() if a == {0}]
    require(len(positive) == 47 and len(negative) == 96 and
            all(p & n != p for p in positive for n in negative), 'Invalid partial monotone relation')
    cert = json.loads((HERE / 'witnesses.json').read_text())
    runpy.run_path(str(HERE / 'witness_check.py'))['check_witnesses'](cert, care, BANK, ROOTS)
    runpy.run_path(str(HERE / 'cases.py'))['verify_cases'](HERE / 'cases.cnf', BANK, [65, 102, 107])
    print('Verified 1,024 graph cells, shard 53, 15 essential donors, 18 corner witnesses, and unsatisfiability of the five-case summary.')
    print('Fixed donor bank: at least 14 gates for three outputs and 16 gates for one merged output.')

if __name__ == '__main__':
    main()
