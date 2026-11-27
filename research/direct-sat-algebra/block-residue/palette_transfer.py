"""Weighted proper four-colorings of one complete bipartite shell block."""



def block_transfer(weights, labels, rank, target, *, pins=None, precision=None):
    """Return the target XOR-fiber sum, exactly or modulo 2**precision.

    The first d rows are the left shore, followed by the d right rows.
    weights[v][c] is a signed integer. labels[v][c] is the parity mask
    contributed by color c at vertex v (a lookup also covers linear labels).
    pins maps vertex indices to required colors. Pinning both bridge ports
    gives a conditional entry; the caller enforces bridge disequality and
    combines block labels by XOR convolution.
    """
    vertices = len(weights)
    if vertices % 2 or len(labels) != vertices or rank < 0:
        raise ValueError("expected equal shores and nonnegative parity rank")
    size = 1 << rank
    if not 0 <= target < size or precision is not None and precision < 0:
        raise ValueError("invalid target or precision")
    if any(len(row) != 4 for row in weights) or any(
        len(row) != 4 or any(x < 0 or x >= size for x in row) for row in labels
    ):
        raise ValueError("expected four entries per row and in-range labels")
    pins = {} if pins is None else pins
    if any(not 0 <= v < vertices or not 0 <= c < 4 for v, c in pins.items()):
        raise ValueError("invalid pin")
    mask = None if precision is None else (1 << (precision + rank)) - 1

    def reduce_int(x):
        return x if mask is None else x & mask

    total = 0
    for character in range(size):
        # Each shore product counts assignments using only the given palette.
        shore = [[1] * 16 for _ in range(2)]
        for v, row in enumerate(weights):
            signed = [
                (-w if (labels[v][c] & character).bit_count() % 2 else w)
                if pins.get(v, c) == c else 0
                for c, w in enumerate(row)
            ]
            side = shore[int(v >= vertices // 2)]
            for palette in range(16):
                allowed = sum(signed[c] for c in range(4) if palette >> c & 1)
                side[palette] = reduce_int(side[palette] * reduce_int(allowed))
        left, right = shore
        # Subset Möbius inversion makes the left palette exact.
        for c in range(4):
            for palette in range(16):
                if palette >> c & 1:
                    left[palette] = reduce_int(left[palette] - left[palette ^ (1 << c)])
        value = sum(left[s] * right[15 ^ s] for s in range(16))
        if (target & character).bit_count() % 2:
            value = -value
        total = reduce_int(total + value)
    # Character orthogonality guarantees exact divisibility after reduction.
    return total // size
