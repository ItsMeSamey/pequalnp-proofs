"""Count assignments avoiding each listed affine system over GF(2)."""


def consistent(equations):
    pivots = {}
    for mask, rhs in equations:
        while mask:
            pivot = mask.bit_length()
            if pivot not in pivots:
                pivots[pivot] = mask, rhs
                break
            row, value = pivots[pivot]
            mask ^= row
            rhs ^= value
        if not mask and rhs:
            return False
    return True


def count_assignments(clauses, n):
    """Each clause requires at least one pair (mask, rhs) to disagree."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    systems = []
    openings = [[] for _ in range(n)]
    endings = []
    impossible = False
    for clause in clauses:
        rows = []
        for mask, rhs in clause:
            if not isinstance(mask, int) or mask < 0 or mask.bit_length() > n:
                raise ValueError("mask must fit in n bits")
            if rhs not in (0, 1) or not isinstance(rhs, int):
                raise ValueError("rhs must be a bit")
            rows.append((mask, rhs))
        if not consistent(rows):
            continue
        rows = [(mask, rhs) for mask, rhs in rows if mask]
        if not rows:
            impossible = True
            continue
        start = min((mask & -mask).bit_length() - 1 for mask, _ in rows)
        openings[start].append(len(systems))
        endings.append(max(mask.bit_length() - 1 for mask, _ in rows))
        systems.append(rows)
    if impossible:
        return 0

    counts = {(): 1}
    for position, opening in enumerate(openings):
        for index in opening:
            selected = index, tuple(rhs for _, rhs in systems[index])
            counts.update({state + (selected,): -weight
                           for state, weight in counts.items()})
        following = {}
        for state, weight in counts.items():
            for bit in (0, 1):
                next_state = []
                equations = []
                for index, residual in state:
                    updated = []
                    for (mask, _), value in zip(systems[index], residual):
                        value ^= bit & (mask >> position)
                        updated.append(value)
                        equations.append((mask >> (position + 1), value))
                    if endings[index] > position:
                        next_state.append((index, tuple(updated)))
                if consistent(equations):
                    key = tuple(next_state)
                    following[key] = following.get(key, 0) + weight
        counts = {key: weight for key, weight in following.items() if weight}
    return counts.get((), 0)
