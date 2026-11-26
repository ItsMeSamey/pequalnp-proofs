"""SAT certificates for the structural lower-bound branches."""
import argparse
from itertools import combinations
from pathlib import Path
from pysat.solvers import Solver
from input import point_obligations
from check import encode

parser = argparse.ArgumentParser()
parser.add_argument('statement', type=Path)
parser.add_argument('case', choices=('five', 'six'))
parser.add_argument('--cnf', type=Path)
parser.add_argument('--proof', type=Path)
args = parser.parse_args()
raw, rows = point_obligations(args.statement)
if args.case == 'five':
    clauses, *_ = encode(raw, rows, 11, 5, abstract=True)
else:
    clauses, masks, *_ = encode(raw, rows, 11, 6, selected=6, abstract=True)
    stars = [sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
    high = max(abs(q) for c in clauses for q in c)
    def fresh():
        global high
        high += 1
        return high
    inside = []
    small = []
    violations = []
    for mask in masks:
        # Each genuine nonraw mask has size at least two: every singleton is raw
        # and a zero mask cannot discriminate any row.
        for omitted in range(13):
            clauses.append([q for d,q in enumerate(mask) if d != omitted])
        small.append(fresh())
        for a,b,c in combinations(mask,3):
            clauses.append([-small[-1], -a, -b, -c])
        membership = []
        for t in stars:
            contained = fresh()
            outside = [q for d,q in enumerate(mask) if not (t>>d&1)]
            for q in outside:
                clauses.append([-contained,-q])
            clauses.append([contained,*outside])
            membership.append(contained)
        inside.append(membership)
        bad = fresh()
        violations.append(bad)
        for contained in membership:
            clauses.append([-bad,-contained])
    for i,j in combinations(range(6),2):
        for t in range(len(stars)):
            bad = fresh()
            violations.append(bad)
            clauses.extend(([-bad,inside[i][t]],[-bad,inside[j][t]]))
    for four in combinations(small,4):
        bad = fresh()
        violations.append(bad)
        clauses.extend([-bad,q] for q in four)
    clauses.append(violations)

with Solver(name='cadical195', bootstrap_with=clauses, with_proof=bool(args.proof)) as solver:
    if args.cnf:
        with args.cnf.open('w') as file:
            print('p cnf',solver.nof_vars(),len(clauses),file=file)
            for c in clauses:
                print(*c,0,file=file)
    assert not solver.solve(), 'a structural violation survived'
    print('UNSAT',args.case,flush=True)
    if args.proof:
        args.proof.write_text('\n'.join(solver.get_proof())+'\n')
