"""Physical exact-plane witnesses for thin-rank parameterized tag menus."""
from itertools import product


def reduce_vector(value, pivots):
    coordinates = 0
    for pivot in sorted(pivots, reverse=True):
        if (value >> pivot) & 1:
            row, mask = pivots[pivot]
            value ^= row
            coordinates ^= mask
    return value, coordinates


def basis(vectors):
    pivots = {}
    indices = []
    for index, value in enumerate(vectors):
        residual, mask = reduce_vector(value, pivots)
        if residual:
            mask ^= 1 << len(indices)
            pivots[residual.bit_length() - 1] = residual, mask
            indices.append(index)
    return pivots, indices


def combine(values, mask):
    result = 0
    while mask:
        bit = mask & -mask
        result ^= values[bit.bit_length() - 1]
        mask ^= bit
    return result


def thick_witness(groups, existing_heights):
    groups = [(v, h, opts) for v, h, opts in groups if v or 0 in opts]
    pivots, selected = basis([v for v, _, _ in groups])
    heights = [groups[i][1] for i in selected]
    masks = []
    extras = []
    gains = list(existing_heights)
    for i, (v, h, _) in enumerate(groups):
        _, mask = reduce_vector(v, pivots)
        gain = h ^ combine(heights, mask)
        if len(basis(gains + [gain])[1]) > len(basis(gains)[1]):
            gains.append(gain)
            masks.append(mask)
            extras.append(i)
    if len(basis(gains)[1]) != 2:
        return None
    # Track joint chart evaluations at the at most two extra sites.
    layers = [{0: None}]
    for pos, i in enumerate(selected):
        next_layer = {}
        for t, original_id in groups[i][2].items():
            delta = sum(t << (2 * j) for j, mask in enumerate(masks)
                        if mask & (1 << pos))
            for state in layers[-1]:
                next_layer.setdefault(state ^ delta, (state, original_id))
        layers.append(next_layer)
    for state in layers[-1]:
        tags = [(state >> (2*j)) & 3 for j in range(len(extras))]
        if any(t not in groups[i][2] for i, t in zip(extras, tags)):
            continue
        result = [groups[i][2][t] for i, t in zip(extras, tags)]
        for layer in reversed(layers[1:]):
            state, edge = layer[state]
            result.append(edge)
        return result
    raise AssertionError("thick-menu union bound failed")


def solve(columns):
    """Return original indices giving exactly the height plane, or None.
    
    Columns have form (private nonnegative integer, two-bit height, two-bit tag).
    """
    menus = {}
    for i, (v, h, t) in enumerate(columns):
        if v < 0 or not 0 <= h < 4 or not 0 <= t < 4:
            raise ValueError("invalid private vector, height or tag")
        menus.setdefault((v, h), {}).setdefault(t, i)
    thin = [(v, h, opts) for (v, h), opts in menus.items() if len(opts) < 3]
    thick = [(v, h, opts) for (v, h), opts in menus.items() if len(opts) >= 3]
    thin_basis, independent = basis([v for v, _, _ in thin])
    masks = [reduce_vector(v, thin_basis)[1] for v, _, _ in thin]
    for chart in product(range(4), repeat=len(independent)):
        active = []
        for (_, _, opts), mask in zip(thin, masks):
            t = combine(chart, mask)
            if t in opts:
                active.append(opts[t])
        pivots, generators = basis([columns[i][0] for i in active])
        height_values = [columns[active[j]][1] for j in generators]
        tag_values = [columns[active[j]][2] for j in generators]
        height_gains = []
        for i in active:
            v, h, _ = columns[i]
            _, mask = reduce_vector(v, pivots)
            height_gains.append(h ^ combine(height_values, mask))
        existing = [height_gains[j] for j in basis(height_gains)[1]]
        reduced = []
        for v, h, opts in thick:
            residual, mask = reduce_vector(v, pivots)
            shift = combine(tag_values, mask)
            reduced.append((residual, h ^ combine(height_values, mask),
                            {t ^ shift: i for t, i in opts.items()}))
        rest = thick_witness(reduced, existing)
        if rest is not None:
            return active + rest
    return None
