"""Compile projection by conditioning independent binary hidden forms."""
from pathlib import Path
import sys

# The rank-one implementation is shared with the sibling research directory.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "rank-projection"))
from check_rank_projection import Circuit, compile_rank_one


def remainder(mask, basis):
    for row in basis:
        mask = min(mask, mask ^ row)
    return mask


def extend(basis, row):
    residual = remainder(row, basis)
    if residual == 0:
        return basis
    return tuple(sorted((*basis, residual), reverse=True))


def minimum_forms(equations, clauses):
    basis = ()
    for row, _ in equations:
        basis = extend(basis, row)

    def search(current, budget):
        for clause in clauses:
            first = 0
            for mask, _ in clause:
                second = remainder(mask, current)
                if second == 0 or second == first:
                    continue
                if first == 0:
                    first = second
                    continue
                if budget == 0:
                    return None
                for choice in (first, second, first ^ second):
                    rest = search(extend(current, choice), budget - 1)
                    if rest is not None:
                        return (choice, *rest)
                return None
        return ()

    budget = 0
    while True:
        result = search(basis, budget)
        if result is not None:
            return result
        budget += 1


def compile_projection(nx, ny, equations, clauses):
    forms = minimum_forms(equations, clauses)
    merged = Circuit(nx)
    root = 0
    for values in range(1 << len(forms)):
        rows = equations + [(mask, ((values >> j) & 1) << nx)
                            for j, mask in enumerate(forms)]
        branch, output = compile_rank_one(nx, ny, rows, clauses)
        wires = list(range(nx + 2))
        for op, left, right in branch.gates:
            wires.append(merged.gate(op, wires[left], wires[right]))
        root = merged.gate("or", root, wires[output])
    return merged, root


def witness(nx, ny, equations, clauses, x):
    rows = list(equations)
    def possible(candidate):
        circuit, output = compile_projection(nx, ny, candidate, clauses)
        return circuit.evaluate(output, x)
    if not possible(rows):
        return None
    assignment = 0
    for i in range(ny):
        bit = int(not possible(rows + [(1 << i, 0)]))
        rows.append((1 << i, bit << nx))
        assignment |= bit << i
    return assignment
