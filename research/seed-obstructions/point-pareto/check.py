"""Exact synthesis on point singleton signatures for the residual cut."""
import argparse
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver
from input import point_obligations


def encode(raw, obligations, width, gates, selected=None, abstract=False, single_hidden=False):
    # Each computed signal is represented by its 13 values on point singletons.
    pool = IDPool()
    allocate = pool.id
    clauses = []
    if single_hidden:
        assert selected == gates - 1
    ordered = gates - int(single_hidden)
    hidden = ordered if single_hidden else -1
    masks = [[allocate() for _ in range(13)] for _ in range(ordered)]
    active_raw = [allocate() for _ in raw]
    active_gates = [] if selected == ordered else [allocate() for _ in masks]
    if selected is None:
        clauses.extend(CardEnc.atmost(active_raw + active_gates, width, vpool=pool).clauses)
    else:
        if active_gates:
            clauses.extend(CardEnc.equals(active_gates, selected, vpool=pool).clauses)
        clauses.extend(CardEnc.atmost(active_raw, width - selected, vpool=pool).clauses)
    for point, negative in obligations:
        choices = [u for mask, u in zip(raw, active_raw) if (mask & point) and not (mask & negative)]
        for index, mask in enumerate(masks):
            witness = allocate()
            clauses.append([-witness, mask[point.bit_length()-1]])
            if active_gates:
                clauses.append([-witness, active_gates[index]])
            for bit in range(13):
                if negative >> bit & 1:
                    clauses.append([-witness, -mask[bit]])
            choices.append(witness)
        clauses.append(choices)

    # Strict unsigned ordering gives unique labels to distinct output masks.
    for i in range(1, ordered):
        equal_prefix = []
        for bit in range(12, -1, -1):
            a, b = masks[i-1][bit], masks[i][bit]
            clauses.append([-e for e in equal_prefix] + [-a, b])
            equal = allocate()
            clauses.extend(([-equal, -a, b], [-equal, a, -b], [equal, a, b], [equal, -a, -b]))
            equal_prefix.append(equal)
        clauses.append([-e for e in equal_prefix])

    if abstract:
        return clauses, masks, active_raw, active_gates

    if single_hidden:
        masks.append([allocate() for _ in range(13)])

    order = {(i, j): allocate() for i, j in combinations(range(gates), 2)}

    def before(i, j):
        return order[i, j] if i < j else -order[j, i]

    for i in range(gates):
        for j in range(gates):
            for k in range(i + 1, gates):
                if i != j != k:
                    clauses.append([-before(i, j), -before(j, k), before(i, k)])
    first_results = sorted({m for a, b in combinations(raw, 2) for m in (a | b, a & b)} - set(raw) - {0})
    for i, output in enumerate(masks):
        options = []
        for m in first_results:
            choice = allocate()
            options.append(choice)
            for d, z in enumerate(output):
                clauses.append([-choice, z if m >> d & 1 else -z])
        for j, parent in enumerate(masks):
            if i == j:
                continue
            for union in ((False, True) if hidden in (i,j) else (j < i,)):
                for raw_mask in raw:
                    choice = allocate()
                    options.append(choice)
                    clauses.append([-choice, before(j, i)])
                    for d, (z, y) in enumerate(zip(output, parent)):
                        if (raw_mask >> d & 1) == union:
                            clauses.append([-choice, z if union else -z])
                        else:
                            clauses.extend(([-choice, -z, y], [-choice, z, -y]))
        for j, k in combinations(range(gates), 2):
            if i in (j,k):
                continue
            for union in (False, True):
                if any(parent != hidden and i != hidden and (parent < i) != union for parent in (j,k)):
                    continue
                choice = allocate()
                options.append(choice)
                clauses.extend(([-choice, before(j, i)], [-choice, before(k, i)]))
                sign = 1 if union else -1
                for a, b, c in zip(masks[j], masks[k], output):
                    a, b, c = sign*a, sign*b, sign*c
                    clauses.extend(([-choice, -a, c], [-choice, -b, c], [-choice, a, b, -c]))
        clauses.append(options)
    return clauses, masks, active_raw, active_gates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('statement', type=Path)
    parser.add_argument('--width', type=int, default=11)
    parser.add_argument('--gates', type=int, default=6)
    parser.add_argument('--selected', type=int)
    parser.add_argument('--single-hidden', action='store_true')
    parser.add_argument('--cnf', type=Path)
    parser.add_argument('--proof', type=Path)
    parser.add_argument('--emit-only', action='store_true')
    parser.add_argument('--require-unsat', action='store_true')
    args = parser.parse_args()
    raw, obligations = point_obligations(args.statement)
    clauses, masks, active_raw, active_gates = encode(raw, obligations, args.width, args.gates, args.selected, single_hidden=args.single_hidden)
    with Solver(name='cadical195', with_proof=bool(args.proof)) as solver:
        for clause in clauses:
            solver.add_clause(clause)
        if args.cnf:
            with args.cnf.open('w') as file:
                print('p cnf', solver.nof_vars(), len(clauses), file=file)
                for clause in clauses:
                    print(*clause, 0, file=file)
        if args.emit_only:
            return
        result = solver.solve()
        print('SAT' if result else 'UNSAT', 'width', args.width, 'gates', args.gates, flush=True)
        if result and args.require_unsat:
            raise SystemExit("A point bank survived")
        if result:
            model = set(solver.get_model())
            values = [sum((q in model) << bit for bit, q in enumerate(mask)) for mask in masks]
            bank = [x for x, q in zip(raw, active_raw) if q in model]
            bank.extend(x for j, x in enumerate(values) if not (args.single_hidden and j == len(values)-1) and (not active_gates or active_gates[j] in model))
            assert len(bank) <= args.width and all(any((x & p) and not (x & n) for x in bank) for p,n in obligations)
            available = set(raw)
            remaining = set(values) - available
            while remaining:
                ready = {x for a,b in combinations(available, 2) for x in (a|b,a&b) if x in remaining}
                assert ready
                available.update(ready)
                remaining -= ready
            print('computed', values, 'boundary', bank)
        elif args.proof:
            args.proof.write_text('\n'.join(solver.get_proof())+'\n')


if __name__ == '__main__':
    main()
