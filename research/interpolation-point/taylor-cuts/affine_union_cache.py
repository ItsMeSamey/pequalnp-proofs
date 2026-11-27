"""Exact union of projected affine cells, with private-coordinate witness lift.

Low n bits are visible, higher bits private. A predicate is existential over
its own private bits; different predicates have disjoint private coordinates.
"""
from affine_cell_energy import AffineCellEnergy, dot, solve


def canonical(n, equations):
    """Unique reduced equation basis for a nonempty affine cell, else None."""
    equations = tuple(equations)
    if solve(n, equations) is None:
        return None
    rows = {}
    for mask, bit in equations:
        for pivot in sorted(rows, reverse=True):
            if mask >> pivot & 1:
                row, rhs = rows[pivot]
                mask ^= row
                bit ^= rhs
        if not mask:
            continue
        new_pivot = mask.bit_length()-1
        for pivot, (row, rhs) in list(rows.items()):
            if row >> new_pivot & 1:
                rows[pivot] = (row ^ mask, rhs ^ bit)
        rows[new_pivot] = mask, bit
    return tuple(rows[p] for p in sorted(rows, reverse=True))


def project(n, total, equations):
    data = solve(total, equations)
    if data is None:
        return None
    point, kernel = data
    visible_mask = (1 << n)-1
    _, normals = solve(n, ((v & visible_mask, 0) for v in kernel))
    return canonical(n, ((v, dot(point, v)) for v in normals))


class AffineUnion:
    def __init__(self, n, private, cells):
        if min(n, private) < 0:
            raise ValueError("negative dimension")
        self.n, self.private = n, private
        self.cells = tuple(tuple(eq) for eq in cells)
        signed = {}
        seen = set()
        self.peak = 0
        for equations in self.cells:
            cell = project(n, n + private, equations)
            if cell is None or cell in seen:
                continue
            seen.add(cell)
            # Indicator update f + 1_C - f*1_C, always using the old f.
            new = dict(signed)
            new[cell] = new.get(cell, 0) + 1
            for existing, coefficient in signed.items():
                overlap = canonical(n, existing + cell)
                if overlap is not None:
                    new[overlap] = new.get(overlap, 0) - coefficient
            signed = {key: v for key, v in new.items() if v}
            self.peak = max(self.peak, len(signed))
        self.terms = tuple((c, eq) for eq, c in signed.items())
        self.interface = AffineCellEnergy(n, self.terms).interface()

    def signature(self, x):
        return sum(dot(x, v) << j for j, v in enumerate(self.interface))

    def value(self, signature):
        if not 0 <= signature < 1 << len(self.interface):
            raise ValueError("invalid quotient signature")
        equations = [(v, signature >> j & 1) for j, v in enumerate(self.interface)]
        x, _ = solve(self.n, equations)
        return sum(c for c, eq in self.terms if all(dot(x,v)==b for v,b in eq))

    def lift(self, x):
        """Return a full witness at this visible x; None means empty fiber."""
        if not 0 <= x < 1 << self.n:
            raise ValueError("invalid visible word")
        pins = tuple((1 << i, x >> i & 1) for i in range(self.n))
        for equations in self.cells:
            data = solve(self.n + self.private, equations + pins)
            if data is not None:
                return data[0]
        return None


def solve_joint(n, requirements):
    """Return (visible,private-extensions), or None when unsatisfiable.

    A negative literal means that NO private extension belongs to its union;
    its witness entry is None. Positive witnesses include their visible bits.
    """
    requirements = tuple(requirements)
    if any(p.n != n or polarity not in (0,1) for p,polarity in requirements):
        raise ValueError("incompatible predicate")
    rows = canonical(n, ((v,0) for p,_ in requirements for v in p.interface))
    base = [v for v,_ in rows]
    for signature in range(1 << len(base)):
        x, _ = solve(n, ((v,signature>>j&1) for j,v in enumerate(base)))
        if all(p.value(p.signature(x)) == polarity for p,polarity in requirements):
            witnesses = tuple(p.lift(x) if polarity else None for p,polarity in requirements)
            assert all(not polarity or w is not None for (_,polarity), w in zip(requirements,witnesses))
            return x,witnesses
    return None
