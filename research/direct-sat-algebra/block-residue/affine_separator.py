"""One-level separator planner for affine flat avoidance."""
from fractions import Fraction


def split_components(flats):
    pivots = {}
    vectors = []
    parents = []
    encoded = []

    def root(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    for rows in flats:
        mapped = []
        support = 0
        for original, rhs in rows:
            mask, code = original, 0
            while mask:
                pivot = mask.bit_length() - 1
                if pivot not in pivots:
                    i = len(vectors)
                    parents.append(i)
                    vectors.append(original)
                    pivots[pivot] = mask, code ^ (1 << i)
                    code = 1 << i
                    break
                pivot_mask, pivot_code = pivots[pivot]
                mask ^= pivot_mask
                code ^= pivot_code
            mapped.append((code, rhs))
            support |= code
        active = [i for i in range(len(vectors)) if support >> i & 1]
        for i in active[1:]:
            parents[root(i)] = root(active[0])
        encoded.append((active[0], mapped))

    groups = {}
    for i in range(len(vectors)):
        groups.setdefault(root(i), []).append(i)
    result = []
    for leader, group in groups.items():
        local = []
        for anchor, rows in encoded:
            if root(anchor) == leader:
                local.append(tuple((sum(((code >> i) & 1) << j for j, i in enumerate(group)), rhs)
                                   for code, rhs in rows))
        result.append(([vectors[i] for i in group], local))
    return result


def best_separator(constraints, dimension, reduce_equation, insert):
    rank = max(map(len, constraints))
    gamma = Fraction((1 << rank) - 1, 1 << (rank - 1))
    bound = gamma ** dimension
    best = None
    normals = set()
    for rows in constraints:
        span = {0}
        for mask, _ in rows:
            span |= {x ^ mask for x in span}
        normals.update(span - {0})
    for normal in sorted(normals):
        slices = []
        cost = 0
        for bit in (0, 1):
            basis = {normal.bit_length() - 1: (normal, bit)}
            flats = []
            for rows in constraints:
                local = {}
                for mask, rhs in rows:
                    if not insert(*reduce_equation(mask, rhs, basis), local):
                        break
                else:
                    if not local:
                        break
                    flats.append(tuple(local.values()))
            else:
                parts = split_components(flats)
                cost += 1 + sum(gamma ** len(vectors) for vectors, _ in parts)
                slices.append((bit, parts))
        if cost < bound:
            best = normal, slices
            bound = cost
    return best
