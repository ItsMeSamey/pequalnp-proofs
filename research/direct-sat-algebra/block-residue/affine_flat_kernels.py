"""Pointwise parallel reduction and witness-preserving private reduction."""


def parallel_kernel(constraints, reduce_equation, insert):
    groups = {}
    for rows in constraints:
        basis = {}
        for mask, rhs in rows:
            insert(mask, rhs, basis)
        canonical = {}
        for pivot in sorted(basis):
            canonical[pivot] = reduce_equation(*basis[pivot], canonical)
        masks = tuple(mask for mask, _ in canonical.values())
        point = sum(rhs << i for i, (_, rhs) in enumerate(canonical.values()))
        groups.setdefault(masks, set()).add(point)

    output = []
    for masks, points in groups.items():
        if len(points) == 1:
            point = next(iter(points))
            output.append(tuple((m, point >> i & 1) for i, m in enumerate(masks)))
            continue
        if len(points) == 1 << len(masks):
            return [()]
        uncovered = set(points)
        while uncovered:
            point = min(uncovered)
            allowed = {point ^ p for p in points}
            frontier = {frozenset((0,))}
            while True:
                larger = set()
                for space in frontier:
                    for direction in allowed - space:
                        other = {x ^ direction for x in space}
                        if other <= allowed:
                            larger.add(space | other)
                if not larger:
                    break
                frontier = larger
            best = min(frontier, key=lambda space: tuple(sorted(space)))
            uncovered.difference_update(point ^ x for x in best)
            orthogonal = {}
            rows = []
            for normal in range(1, 1 << len(masks)):
                if any((normal & x).bit_count() % 2 for x in best):
                    continue
                if not reduce_equation(normal, 0, orthogonal)[0]:
                    continue
                insert(normal, 0, orthogonal)
                mask = 0
                for i, coefficient in enumerate(masks):
                    if normal >> i & 1:
                        mask ^= coefficient
                rows.append((mask, (normal & point).bit_count() % 2))
            output.append(tuple(rows))
    return output


def private_equation(constraints, reduce_equation, insert):
    for i, rows in enumerate(constraints):
        outside = {}
        for j, other in enumerate(constraints):
            if j != i:
                for mask, _ in other:
                    insert(mask, 0, outside)
        for mask, rhs in rows:
            if reduce_equation(mask, 0, outside)[0]:
                return mask, rhs ^ 1
    return None
