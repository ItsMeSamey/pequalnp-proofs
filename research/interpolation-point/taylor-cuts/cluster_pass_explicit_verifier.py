"""Small-domain reference verifier. Uses no production pass or elimination code."""
from itertools import product


def rank(columns):
    pivots = {}
    for x in columns:
        while x:
            axis = x.bit_length() - 1
            if axis not in pivots:
                pivots[axis] = x
                break
            x ^= pivots[axis]
    return len(pivots)


def spans(masks, candidates, column):
    columns = [column(m) for m in masks]
    return rank(columns) == rank(columns + [column(m) for m in candidates])


def verify(n, size, passes, order, lengths, certificate, *, start=None, closing=None):
    """Replay an explicit-list certificate. Intended only for bounded test fixtures."""
    try:
        states = tuple(range(size))
        if type(n) is not int or type(size) is not int or n < 0 or size < 1:
            return False
        if sorted(order) != list(range(1, n+1)) or any(type(v) is not int for v in order):
            return False
        positions = {v: i for i, v in enumerate(order)}
        if start is not None and (type(start) is not int or start not in states):
            return False
        closing = states if closing is None else closing
        def permutation(p):
            return sorted(p) == list(states) and all(type(x) is int for x in p)
        if not permutation(closing):
            return False
        for forward, gates in passes:
            if type(forward) is not bool:
                return False
            last = -1
            for lit, p, q in gates:
                if type(lit) is not int or abs(lit) not in positions or not permutation(p) or not permutation(q):
                    return False
                slot = positions[abs(lit)]
                slot = slot if forward else n-1-slot
                if slot < last:
                    return False
                last = slot
        if any(type(k) is not int or k < 1 for k in lengths) or sum(lengths) != len(passes):
            return False
        groups = []
        first = 0
        for k in lengths:
            groups.append(range(first, first+k))
            first += k

        full = (1 << n) - 1
        starts = states if start is None else (start,)
        def proper(mask, allowed):
            return type(mask) is int and mask >= 0 and not mask & ~allowed

        def execute(j, mask, state, allowed):
            for lit, p, q in passes[j][1]:
                bit = 1 << (abs(lit)-1)
                if allowed & bit:
                    truth = bool(mask & bit) != (lit < 0)
                    state = (q if truth else p)[state]
            return state

        def closed(prefixes, suffix, state):
            initial = state
            for mask, group in zip(prefixes, groups):
                for j in group:
                    state = execute(j, mask | suffix, state, full)
            return closing[state] == initial

        tag, *rest = certificate
        if tag == "sat":
            mask, s = rest
            return proper(mask, full) and type(s) is int and s in starts and closed([0]*len(groups), mask, s)
        if tag != "unsat":
            return False
        prefix, suffix = rest
        if len(prefix) != n+1 or len(suffix) != n+1:
            return False

        left = 0
        for i, level in enumerate(prefix):
            if i:
                bit = 1 << (order[i-1]-1)
                left |= bit
            if len(level) != len(groups):
                return False
            for g, (group, reps) in enumerate(zip(groups, level)):
                if not isinstance(reps, (tuple, list)) or not all(proper(m, left) for m in reps):
                    return False
                candidates = [0] if i == 0 else [m | extra for m in prefix[i-1][g] for extra in (0, bit)]
                def tensor_column(mask):
                    # Enumerate every input/output coordinate of every permutation factor.
                    column = 0
                    for index, coords in enumerate(product(states, repeat=2*len(group))):
                        if all(execute(j, mask, coords[2*h], left) == coords[2*h+1]
                               for h, j in enumerate(group)):
                            column |= 1 << index
                    return column
                if not spans(reps, candidates, tensor_column):
                    return False

        right = 0
        for i in range(n, -1, -1):
            if i < n:
                bit = 1 << (order[i]-1)
                right |= bit
            reps = suffix[i]
            if not isinstance(reps, (tuple, list)) or not all(proper(m, right) for m in reps):
                return False
            candidates = [0] if i == n else [m | extra for m in suffix[i+1] for extra in (0, bit)]
            def observable(mask):
                column = 0
                index = 0
                for prefix_masks in product(*prefix[i]):
                    for s in starts:
                        if closed(prefix_masks, mask, s):
                            column |= 1 << index
                        index += 1
                return column
            if not spans(reps, candidates, observable):
                return False
        return not any(closed([0]*len(groups), mask, s) for mask in suffix[0] for s in starts)
    except (TypeError, ValueError, IndexError, KeyError):
        return False
