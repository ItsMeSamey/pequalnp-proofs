"""Deterministic affine flat avoidance. Masks are nonnegative integers, bit i is x_i."""
from functools import lru_cache
from itertools import product
from affine_separator import best_separator
from affine_flat_kernels import parallel_kernel, private_equation


def reduce_equation(mask, rhs, basis):
    for pivot in sorted(basis, reverse=True):
        if mask >> pivot & 1:
            row, value = basis[pivot]
            mask ^= row
            rhs ^= value
    return mask, rhs


def insert(mask, rhs, basis):
    mask, rhs = reduce_equation(mask, rhs, basis)
    if mask:
        basis[mask.bit_length() - 1] = mask, rhs
    return bool(mask or not rhs)


@lru_cache(maxsize=None)
def block_cover(rank, length):
    alphabet = range(1, 1 << rank)
    words = list(product(alphabet, repeat=length))
    targets = set(words)
    result = []
    while targets:
        def hits(word):
            return {v for v in targets if all((a & b).bit_count() % 2
                                               for a, b in zip(word, v))}
        best = max(words, key=lambda word: len(hits(word)))
        targets -= hits(best)
        result.append(best)
    return tuple(result)


def solve(n, flats, seed=(), *, kernels=True, separator=True):
    """Return a satisfying n-bit integer or None. seed equations must hold.

    Each flat is an iterable of (coefficient mask, right-hand-side bit).
    A feasible point must violate at least one equation of every flat.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError("dimension must be a nonnegative integer")

    def checked(rows):
        rows = tuple(rows)
        for mask, rhs in rows:
            if not isinstance(mask, int) or mask < 0 or mask.bit_length() > n or rhs not in (0, 1):
                raise ValueError("invalid Boolean equation")
        return rows

    original = tuple(checked(flat) for flat in flats)
    seed = checked(seed)
    initial = {}
    for mask, rhs in seed:
        if not insert(mask, rhs, initial):
            return None
    block_length = (n - len(initial) + 1).bit_length()

    def search(basis, active, at_root=False):
        while True:
            constraints = []
            unit = None
            for flat in active:
                local = {}
                for mask, rhs in flat:
                    mask, rhs = reduce_equation(mask, rhs, basis)
                    if not insert(mask, rhs, local):
                        break
                else:
                    if not local:
                        return None
                    rows = tuple(local.values())
                    if len(rows) == 1:
                        mask, rhs = rows[0]
                        unit = mask, rhs ^ 1
                        break
                    constraints.append(rows)
            if unit is None and kernels:
                constraints = parallel_kernel(constraints, reduce_equation, insert)
                active = constraints
                if any(not rows for rows in constraints):
                    return None
                for rows in constraints:
                    if len(rows) == 1:
                        mask, rhs = rows[0]
                        unit = mask, rhs ^ 1
                        break
                if unit is None:
                    unit = private_equation(constraints, reduce_equation, insert)
            if unit is None:
                break
            insert(*unit, basis)

        def backlift(equations):
            witness = 0
            for pivot in sorted(equations):
                mask, rhs = equations[pivot]
                witness |= (rhs ^ ((mask & witness).bit_count() % 2)) << pivot
            return witness

        if not constraints:
            return backlift(basis)
        if kernels and separator and at_root:
            plan = best_separator(constraints, n-len(basis), reduce_equation, insert)
            if plan is not None:
                normal, slices = plan
                for bit, parts in slices:
                    equations = basis.copy()
                    insert(normal, bit, equations)
                    for vectors, gates in parts:
                        value = solve(len(vectors), gates, separator=False)
                        if value is None:
                            break
                        for i, vector in enumerate(vectors):
                            insert(vector, value >> i & 1, equations)
                    else:
                        return backlift(equations)
                return None

        rank = max(map(len, constraints))
        span = {}
        family = []
        for rows in constraints:
            if len(rows) == rank:
                trial = span.copy()
                for mask, _ in rows:
                    insert(mask, 0, trial)
                if len(trial) == len(span) + rank:
                    span = trial
                    family.append(rows)
        r = len(family)
        d = n - len(basis)
        size = (1 << rank) - 1
        prev = (1 << (rank - 1)) - 1
        rem = d - rank * r
        full = (size**r * prev**rem << ((rank-1)*d)) <= (size**d << ((rank-2)*rem))
        if full:
            choices = product(range(1, size + 1), repeat=r)
        else:
            blocks = [block_cover(rank, min(block_length, r-start))
                      for start in range(0, r, block_length)]
            choices = (tuple(v for block in selection for v in block)
                       for selection in product(*blocks))
        for choice in choices:
            child = basis.copy()
            for value, rows in zip(choice, family):
                if full:
                    for i, (mask, rhs) in enumerate(rows):
                        insert(mask, rhs ^ (value >> i & 1), child)
                else:
                    total_mask, total_rhs = 0, 1
                    for i, (mask, rhs) in enumerate(rows):
                        if value >> i & 1:
                            total_mask ^= mask
                            total_rhs ^= rhs
                    insert(total_mask, total_rhs, child)
            witness = search(child, constraints)
            if witness is not None:
                return witness
        return None

    return search(initial, original, at_root=True)
