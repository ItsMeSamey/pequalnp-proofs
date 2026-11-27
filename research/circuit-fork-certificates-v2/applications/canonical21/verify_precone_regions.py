#!/usr/bin/env python3
"""Rebuild the five-region obstruction and independently check its RUP proof."""
import argparse
import hashlib
from ordered_region import encode_ordered
from region_rup import RupChecker
import json
from collections import defaultdict
from pathlib import Path

CARE_SHA256 = '16199778bdce2ba5ae48b6c55ec730f73f7059c0e58857ec7fa837f9b58f8879'
CNF_SHA256 = 'a839cb8c6206553359dfa5014a295cd5222b7af2f1e0c8b84d5eb4b23ae7ad08'


def encode(path):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != CARE_SHA256:
        raise ValueError('projected care source digest mismatch')
    care = dict(json.loads(raw)['care'])
    desc = [(x,y) for x in care if care[x] for y in care if not care[y] and x & y == x]
    lows, highs = {x for x,y in desc}, {y for x,y in desc}
    supported = {h & ~l for h in highs for l in lows if (h & ~l).bit_count() == 1}
    if supported != {1 << i for i in range(21)}:
        raise ValueError('missing essential feature')
    highs = sorted(h for h in highs if not any(z != h and z & h == z for z in highs))
    lows = sorted(l for l in lows if not any(z != l and z & l == l for z in lows))
    clauses, names = encode_ordered(highs,lows,21,5)
    header = f'p cnf {len(names)} {len(clauses)}\n'
    dimacs = header + ''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    if hashlib.sha256(dimacs.encode('ascii')).hexdigest() != CNF_SHA256:
        raise ValueError('rebuilt five-region formula digest mismatch')
    return len(names),clauses,dimacs


def main():
    p=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    p.add_argument('--care',type=Path,default=here/'paid26-alias-ac6.json')
    p.add_argument('--proof',type=Path,default=here/'precone-region-5.drup')
    p.add_argument('--write-cnf',type=Path)
    a=p.parse_args()
    n,clauses,dimacs=encode(a.care)
    if a.write_cnf:
        a.write_cnf.write_bytes(dimacs.encode('ascii'))
    additions=RupChecker(n,clauses).verify(a.proof)
    print(f'Verified {len(clauses)} clauses and {additions} RUP additions. '
          'Five regions are infeasible. The sole-NOT operand requires at least 25 gates.')


if __name__=='__main__':
    try:
        main()
    except (OSError,ValueError) as e:
        raise SystemExit(str(e))
