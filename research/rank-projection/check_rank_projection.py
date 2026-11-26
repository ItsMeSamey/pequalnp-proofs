"""Compile a binary rank-one projection and check it against exhaustive search.

A form is (ymask, xform), representing parity(ymask & y) XOR
parity(xform & x) XOR bit(xform, nx). Equations require value zero.
Each residual clause requires at least one of its forms to be one.
"""
from __future__ import annotations

from itertools import product
from random import Random


Form = tuple[int, int]


class Circuit:
    """Wire 0 is false, wire 1 is true, and wire 2+i is observed bit i."""

    def __init__(self, nx: int):
        self.nx = nx
        self.gates: list[tuple[str, int, int]] = []
        self._wires: dict[tuple[str, int, int], int] = {}

    def gate(self, op: str, a: int, b: int) -> int:
        a, b = sorted((a, b))
        if op == "and":
            if a == 0 or a == b:
                return a
            if a == 1:
                return b
        elif op == "or":
            if a == 1 or a == b:
                return a
            if a == 0:
                return b
        elif op == "xor":
            if a == b:
                return 0
            if a == 0:
                return b
        else:
            raise ValueError(f"unknown operation {op}")
        key = op, a, b
        if key not in self._wires:
            self._wires[key] = 2 + self.nx + len(self.gates)
            self.gates.append(key)
        return self._wires[key]

    def negate(self, a: int) -> int:
        return self.gate("xor", 1, a)

    def mux(self, select: int, new: int, old: int) -> int:
        diff = self.gate("xor", new, old)
        return self.gate("xor", old, self.gate("and", select, diff))

    def affine(self, xform: int) -> int:
        wire = (xform >> self.nx) & 1
        for i in range(self.nx):
            if xform & (1 << i):
                wire = self.gate("xor", wire, 2 + i)
        return wire

    def evaluate(self, output: int, x: int) -> int:
        if not 0 <= x < 1 << self.nx:
            raise ValueError("observed assignment out of range")
        wires = [0, 1] + [(x >> i) & 1 for i in range(self.nx)]
        for op, a, b in self.gates:
            if op == "and":
                result = wires[a] & wires[b]
            elif op == "or":
                result = wires[a] | wires[b]
            else:
                result = wires[a] ^ wires[b]
            wires.append(result)
        return wires[output]


def parameterize(ny: int, equations: list[Form]) -> tuple[list[Form], list[int]]:
    """Keep nonpivot hidden bits free and return the observed consistency rows."""
    rows = list(equations)
    pivots = {}
    for j in range(ny):
        k = len(pivots)
        found = next((i for i in range(k, len(rows)) if rows[i][0] & (1 << j)), None)
        if found is None:
            continue
        rows[k], rows[found] = rows[found], rows[k]
        mask, offset = rows[k]
        for i, (other_mask, other_offset) in enumerate(rows):
            if i != k and other_mask & (1 << j):
                rows[i] = other_mask ^ mask, other_offset ^ offset
        pivots[j] = k

    hidden_forms = []
    for j in range(ny):
        if j in pivots:
            mask, offset = rows[pivots[j]]
            hidden_forms.append((mask ^ (1 << j), offset))
        else:
            hidden_forms.append((1 << j, 0))
    return hidden_forms, [offset for mask, offset in rows if mask == 0]


def compile_rank_one(nx: int, ny: int, equations: list[Form],
                     clauses: list[list[Form]]) -> tuple[Circuit, int]:
    """Compile exact projection, raising ValueError outside the rank promise."""
    if nx < 0 or ny < 0:
        raise ValueError("negative variable count")
    for group in [equations, *clauses]:
        for mask, form in group:
            if not (0 <= mask < 1 << ny and 0 <= form < 1 << (nx + 1)):
                raise ValueError("form references an undeclared bit")

    circuit = Circuit(nx)
    hidden_forms, consistency = parameterize(ny, equations)
    output = 1
    for offset in consistency:
        output = circuit.gate("and", output, circuit.negate(circuit.affine(offset)))

    # Each entry is a circuit wire. At a fixed X, pivot_rows[j][j] is one
    # precisely when the incremental echelon basis already has pivot j.
    pivot_rows = [[0] * (ny + 1) for _ in range(ny)]
    for clause in clauses:
        common = 0
        offsets = []
        already_true = 0
        for raw_mask, form in clause:
            latent = 0
            while raw_mask:
                bit = raw_mask & -raw_mask
                hidden_mask, hidden_offset = hidden_forms[bit.bit_length() - 1]
                latent ^= hidden_mask
                form ^= hidden_offset
                raw_mask ^= bit
            wire = circuit.affine(form)
            if latent == 0:
                already_true = circuit.gate("or", already_true, wire)
            else:
                if common and common != latent:
                    raise ValueError("residual clause has hidden rank greater than one")
                common = latent
                offsets.append(wire)
        if not offsets:
            output = circuit.gate("and", output, already_true)
            continue

        reference = offsets[0]
        for offset in offsets[1:]:
            opposite = circuit.gate("xor", reference, offset)
            already_true = circuit.gate("or", already_true, opposite)
        active = circuit.negate(already_true)
        row = [active if common & (1 << j) else 0 for j in range(ny)]
        row.append(circuit.gate("and", active, circuit.negate(reference)))

        for j in range(ny):
            old = pivot_rows[j]
            insert = circuit.gate("and", row[j], circuit.negate(old[j]))
            eliminate = circuit.gate("and", row[j], old[j])
            pivot_rows[j] = [circuit.mux(insert, new, prev) for new, prev in zip(row, old)]
            # Store and consume a row with a new pivot. Otherwise XOR the old
            # pivot row when needed. Both operations read the previous basis.
            keep = circuit.negate(insert)
            next_row = []
            for val, prev in zip(row, old):
                correction = circuit.gate("and", eliminate, prev)
                next_row.append(circuit.gate("and", keep, circuit.gate("xor", val, correction)))
            row = next_row
        output = circuit.gate("and", output, circuit.negate(row[-1]))
    return circuit, output


def brute(nx: int, ny: int, equations: list[Form], clauses: list[list[Form]], x: int) -> bool:
    observed = x | (1 << nx)
    for y in range(1 << ny):
        def value(lit: Form) -> int:
            ymask, xform = lit
            return ((ymask & y).bit_count() + (xform & observed).bit_count()) % 2

        if all(value(row) == 0 for row in equations) and all(any(map(value, c)) for c in clauses):
            return True
    return False


def check_compiler() -> int:
    rng = Random(73522)
    checked = 0

    def compare(nx, ny, rows, clauses):
        nonlocal checked
        circuit, root = compile_rank_one(nx, ny, rows, clauses)
        for x in range(1 << nx):
            if circuit.evaluate(root, x) != brute(nx, ny, rows, clauses, x):
                raise AssertionError((nx, ny, rows, clauses, x))
            checked += 1

    compare(0, 0, [], [])
    compare(0, 0, [], [[]])
    compare(1, 0, [(0, 1)], [])
    compare(0, 1, [(1, 0), (1, 1)], [])
    compare(1, 2, [(3, 1)], [[(1, 0), (2, 0)]])
    try:
        compile_rank_one(0, 2, [], [[(1, 0), (2, 0)]])
    except ValueError as error:
        if "hidden rank" not in str(error):
            raise
    else:
        raise AssertionError("compiler accepted an out-of-promise clause")

    for _ in range(500):
        nx, ny = rng.randrange(5), rng.randrange(6)
        rows = [(rng.randrange(1 << ny), rng.randrange(1 << (nx + 1)))
                for _ in range(rng.randrange(ny + 2))]
        clauses = []
        for _ in range(rng.randrange(13)):
            base = rng.randrange(1 << ny)
            clause = []
            for _ in range(rng.randrange(6)):
                mask = rng.choice((0, base))
                offset = rng.randrange(1 << (nx + 1))
                # Row-space perturbations can change the raw masks without
                # changing the latent forms on the affine solution space.
                for other_mask, other_offset in rows:
                    if rng.randrange(2):
                        mask ^= other_mask
                        offset ^= other_offset
                clause.append((mask, offset))
            clauses.append(clause)
        compare(nx, ny, rows, clauses)
    return checked


def encode_clause(terms: tuple[int, int, int], selectors: tuple[int, int, int],
                  unique: bool) -> list[tuple[int, int]]:
    """Generate Horn clauses for fresh selectors; impose their odd parity separately."""
    implications = [(-s, term) for s, term in zip(selectors, terms)]
    if unique:
        for i, s in enumerate(selectors):
            implications.extend((-s, -previous) for previous in terms[:i])
    return implications


def check_reduction() -> int:
    checked = 0
    # Includes both signs, repeated variables, tautologies, and all source assignments.
    for terms in product((-2, -1, 1, 2), repeat=3):
        for unique in (False, True):
            implications = encode_clause(terms, (3, 4, 5), unique)
            if any(sum(lit > 0 for lit in clause) > 1 for clause in implications):
                raise AssertionError("non-Horn target clause")
            for x in range(4):
                def holds(lit, assignment):
                    return bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)

                source = any(holds(lit, x) for lit in terms)
                extensions = 0
                for selector_bits in range(8):
                    if selector_bits.bit_count() % 2 != 1:
                        continue
                    assignment = x | (selector_bits << 2)
                    if all(any(holds(lit, assignment) for lit in c) for c in implications):
                        extensions += 1
                if bool(extensions) != source or (unique and extensions != int(source)):
                    raise AssertionError((terms, unique, x, extensions))
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"Rank-one compiler agreed with exhaustive projection on {check_compiler()} observations.")
    print(f"Both signed reduction variants passed all {check_reduction()} clause-assignment checks.")
