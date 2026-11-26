"""Verify a sparse perturbation missed by the mask LP before a forced-zero deduction."""
from fractions import Fraction
from mask_lp import compiler, relaxation, x, z


def check(holes, others):
    normals, offset, marker, _ = compiler(holes, others)
    if not marker:
        return False
    old_n = len(normals)
    edge = (marker & -marker).bit_length() - 1
    t = old_n
    corners = [t+1+i for i in range(4)]
    parity = sum(1 << i for i in corners)
    modified = normals.copy()
    modified[edge] ^= 1 << t
    modified.append(parity)
    pairs = [(1 << corners[(i-1) % 4]) | (1 << corners[(i+1) % 4]) for i in range(4)]
    modified.extend(pairs)
    offset |= sum(1 << i for i in [t] + corners)
    ge, eq = relaxation(modified, offset, marker)

    # Exact Boolean assignment on the old rows and their shared switch.
    block = (1 << t) | (1 << edge)
    fractional = {None: 1}
    for i in range(t+1):
        fractional[x(i)] = (block >> i) & 1
    masks = {marker, 1 << t}
    for i, a in enumerate(modified[:t]):
        masks.update((a, a ^ (1 << i)))
    for m in masks:
        fractional[z(m)] = (m & block).bit_count() % 2

    # A fractional local solution on the switch gadget.
    fractional[z(parity)] = 1
    fractional[z(parity ^ (1 << t))] = 0
    for i, a in zip(corners, pairs):
        fractional[x(i)] = Fraction(1,2)
        fractional[z(a)] = 1
        fractional[z(a ^ (1 << i))] = Fraction(1,2)
    def ev(q):
        return sum(coeff * fractional[var] for var, coeff in q.items())
    assert all(ev(q) >= 0 for q in ge.values())
    assert all(ev(q) == 0 for q in eq.values())

    # Check the two-line algebraic certificate for t=0 as Boolean monomials.
    summed = set()
    for i, a in zip(corners, pairs):
        ri = {1 << i} | {(1 << i) | (1 << j) for j in corners if a & (1 << j)}
        summed.symmetric_difference_update(ri)
    assert summed == {1 << i for i in corners}
    gate = {1 << t} | {(1 << t) | (1 << i) for i in corners}
    assert {term | (1 << t) for term in summed} ^ gate == {1 << t}
    assert [a & ~(1 << t) for a in modified[:old_n]] == normals
    return True


if __name__ == '__main__':
    h = 3
    optional = [(p, v) for p in range(h+1) for v in range(h) if p != v]
    n = sum(check(h, [e for j,e in enumerate(optional) if mask & (1 << j)])
            for mask in range(1 << len(optional)))
    print(f"Verified {n} rational witnesses and forced-zero repairs of the mask LP.")
