"""Read exact XOR, inversion, and conjunction macros from an ordered NAND DAG."""
from dataclasses import dataclass

from affine_independence_portfolio import basis
from primitive_rewrite_chain import _inputs, evaluate


@dataclass(frozen=True)
class AffineResult:
    equations: tuple  # (packed coefficient mask, right-hand side)
    count: int
    witness: int | None


def solve_affine_macros(n, gates, output):
    """Recognize conjunctions of affine expressions, or return None.

    The low bit in an internal affine expression is its constant. The other
    bits use the original packed assignment order. No target rows are supplied.
    """
    gates = _inputs(n, gates, output)
    forms = {-1: 0, -2: 1}
    forms.update((i, 1 << (n-i)) for i in range(n))
    for w, (left, right) in enumerate(gates, n):
        if left == right and left in forms:
            forms[w] = forms[left] ^ 1
            continue
        if left < n or right < n:
            continue
        a, middle = gates[left-n]
        b, other_middle = gates[right-n]
        if (middle == other_middle and middle >= n and gates[middle-n] == (a, b)
                and a in forms and b in forms):
            forms[w] = forms[a] ^ forms[b]

    stack, seen, rows = [output], set(), []
    while stack:
        w = stack.pop()
        if w in seen:
            continue
        seen.add(w)
        if w in forms:
            equation = forms[w] ^ 1  # component must equal one
            if equation:
                rows.append(equation)
            continue
        a, b = gates[w-n]
        if a != b or a < n:
            return None
        left, right = gates[a-n]
        stack.extend((right, left))

    equations = tuple((row >> 1, row & 1) for row in rows)
    pivots = basis(rows)  # eliminate augmented rows; a low-bit pivot is 0=1
    if 1 in pivots:
        return AffineResult(equations, 0, None)
    witness = 0
    for row in reversed(pivots):
        mask, rhs = row >> 1, row & 1
        if ((mask & witness).bit_count() & 1) != rhs:
            witness |= 1 << (mask.bit_length()-1)
    if evaluate(n, gates, output, witness) != 1:
        raise AssertionError('reconstructed model rejected by original NAND circuit')
    return AffineResult(equations, 1 << (n-len(pivots)), witness)
