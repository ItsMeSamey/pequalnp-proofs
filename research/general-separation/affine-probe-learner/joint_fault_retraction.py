"""Safe affine consequences of explicit NAND macros and joint retraction.

Original coordinates are packed most-significant first. A row (m,b) means
parity(m & x) == b. Constants -1 and -2 mean zero and one.
"""
from dataclasses import dataclass

from binary_fault_retraction import Gamma, _accepts
from primitive_rewrite_chain import _inputs


def affine_conjuncts(n, gates, output):
    """Return recognized top conjuncts as affine equations on original inputs.

    Walk through AND implemented as double NAND. At each node prefer a
    recognized affine expression; an opaque leaf contributes no constraint.
    """
    gates = _inputs(n, gates, output)
    forms = {-1: 0, -2: 1}
    forms.update((i, 1 << (n-i)) for i in range(n))
    for w, (left, right) in enumerate(gates, n):
        if left == right and left in forms:
            forms[w] = forms[left] ^ 1
            continue
        if left >= n and right >= n:
            a, middle = gates[left-n]
            b, other_middle = gates[right-n]
            if (middle == other_middle and middle >= n and gates[middle-n] == (a, b)
                    and a in forms and b in forms):
                forms[w] = forms[a] ^ forms[b]

    rows = {}
    seen = set()
    stack = [output]
    while stack:
        w = stack.pop()
        if w in seen:
            continue
        seen.add(w)
        if w in forms:
            mask, rhs = forms[w] >> 1, (forms[w] & 1) ^ 1
            if mask or rhs:
                rows[mask, rhs] = None
        else:
            left, right = gates[w-n]
            if left == right and left >= n:
                a, b = gates[left-n]
                stack.extend((b, a))
    return tuple(rows)


def _satisfies(rows, x):
    return all(((m & x).bit_count() & 1) == b for m, b in rows)


@dataclass(frozen=True)
class JointRetracted:
    n: int
    gates: tuple
    output: int
    clauses: tuple
    rows: tuple
    anchor: int

    def accepts(self, x):
        return _accepts(self.n, self.clauses, x) and _satisfies(self.rows, x)

    def lift(self, x):
        return x if self.accepts(x) else self.anchor


def compile_joint_retraction(n, gates, output, gamma, rows, anchor):
    """Compile F(R(x)), where R fixes every joint model and maps others to anchor.

    With m clauses, r Gaussian rows, L total nonzero row coefficients, and s
    source gates, the result has at most s + 3n + 3m + 4L + 3r NAND gates.
    No new input coordinates are introduced.
    """
    gates = _inputs(n, gates, output)
    if not isinstance(gamma, Gamma) or gamma.n != n:
        raise ValueError('incompatible Gamma')
    clauses = gamma.clauses
    rows = tuple((m, b) for m, b in rows)
    for m, b in rows:
        if type(m) is not int or m < 0 or m.bit_length() > n or type(b) is not int or b not in (0, 1):
            raise ValueError('invalid Gaussian row')
    if not _accepts(n, clauses, anchor) or not _satisfies(rows, anchor):
        raise ValueError('anchor violates joint constraints')
    if not clauses and not rows:
        return JointRetracted(n, gates, output, clauses, rows, anchor)

    compiled = []
    def nand(a, b):
        compiled.append((a, b))
        return n + len(compiled) - 1

    negatives = {-1: -2, -2: -1}
    def inv(a):
        if a not in negatives:
            negatives[a] = nand(a, a)
        return negatives[a]

    def conjunction(a, b):
        if a == -2:
            return b
        if b == -2:
            return a
        inverse = nand(a, b)
        return nand(inverse, inverse)

    def literal(i, sign):
        return i if sign else inv(i)

    predicate = -2
    for clause in clauses:
        if len(clause) == 1:
            term = literal(*clause[0])
        else:
            (i, a), (j, b) = clause
            term = nand(literal(i, a ^ 1), literal(j, b ^ 1))
        predicate = conjunction(predicate, term)
    for mask, rhs in rows:
        parity = -1
        while mask:
            bit = mask & -mask
            wire = n-bit.bit_length()
            if parity == -1:
                parity = wire
            else:
                middle = nand(parity, wire)
                parity = nand(nand(parity, middle), nand(wire, middle))
            mask ^= bit
        predicate = conjunction(predicate, parity if rhs else inv(parity))

    if predicate == -2:
        return JointRetracted(n, gates, output, clauses, rows, anchor)
    wires = {-1: -1, -2: -2}
    for i in range(n):
        if anchor & (1 << (n-1-i)):
            wires[i] = nand(predicate, inv(i))
        else:
            wires[i] = conjunction(predicate, i)
    for w, (a, b) in enumerate(gates, n):
        wires[w] = nand(wires[a], wires[b])
    return JointRetracted(n, tuple(compiled), wires[output], clauses, rows, anchor)
