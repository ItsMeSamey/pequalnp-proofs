"""Count a packed vector quadratic fiber by parallel affine slices."""
from quadratic_target import (affine_domain, apply_basis, evaluate_anf,
                              insert, interpolate, reduce_vector)


def split_basis(n, pairs):
    """Return complementary directions followed by common isotropic directions."""
    basis = [1 << i for i in range(n)]
    complement = []
    while basis:
        def quadratic(x):
            return evaluate_anf(0, [0] * n, pairs, apply_basis(basis, x))

        restricted = interpolate(quadratic, len(basis))[2]
        if not restricted:
            break
        bit = next(iter(restricted.values())) & -next(iter(restricted.values()))
        rows = [0] * len(basis)
        for (i, j), value in restricted.items():
            if value & bit:
                rows[i] ^= 1 << j
                rows[j] ^= 1 << i
        _, kernel, pivots = affine_domain(len(basis), ((r, 0) for r in rows))
        complement.extend(basis[i] for i in pivots)
        basis = [apply_basis(basis, r) for r in kernel]
    return complement, basis


def count(n, constant, linear, pairs, target, cap=None):
    """Return (count, witness, greedy codimension); None count means cap exceeded."""
    complement, flat = split_basis(n, pairs)
    cost = len(complement)
    if cap is not None and cost > cap:
        return None, None, cost
    total = 0
    witness = None
    for mask in range(1 << cost):
        origin = apply_basis(complement, mask)
        base = evaluate_anf(constant, linear, pairs, origin)
        rows = {}
        for j, v in enumerate(flat):
            delta = evaluate_anf(constant, linear, pairs, origin ^ v) ^ base
            insert(delta, 1 << j, rows)
        remainder, preimage = reduce_vector(target ^ base, rows)
        if not remainder:
            total += 1 << (len(flat) - len(rows))
            if witness is None:
                witness = origin ^ apply_basis(flat, preimage)
    return total, witness, cost
