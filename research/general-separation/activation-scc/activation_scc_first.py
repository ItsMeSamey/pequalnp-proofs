"""One-readout activation solver parameterized only by constant-input SCC ranks."""
from activation_scc_moments import bits, blocks, correction, insert


def dot(a, b):
    return (a & b).bit_count() & 1


def affine_rows(equations, domain):
    """A point and nullspace generators in the original physical bit indexing."""
    p = {}
    for row, target in equations:
        a = row & domain
        b = target
        while a:
            i = a.bit_length() - 1
            if i not in p:
                p[i] = a, b
                break
            h, v = p[i]
            a ^= h
            b ^= v
        else:
            if b:
                return None
    def lift(x, homogeneous):
        for i in sorted(p):
            h, v = p[i]
            if dot(h, x) ^ (0 if homogeneous else v):
                x |= 1 << i
        return x
    free = domain
    for i in p:
        free ^= 1 << i
    return lift(0, False), [lift(1 << i, True) for i in bits(free)]


def fixed_generators(rows, block, rhs):
    gauge = correction(rows, block) ^ block
    transformed = [((rows[i] ^ (gauge & (1 << i))) & block) for i in bits(block)]
    # Encode each physical row by coefficients in an echelon row basis.
    pivots = {}
    basis_rows = []
    coordinates = []
    for row in transformed:
        a = row
        code = 0
        while a:
            i = a.bit_length() - 1
            if i not in pivots:
                label = 1 << len(basis_rows)
                pivots[i] = a, label
                basis_rows.append(a)
                code ^= label
                break
            h, label = pivots[i]
            a ^= h
            code ^= label
        coordinates.append(code)
    for z in range(1 << len(basis_rows)):
        allowed = 0
        for i, form in zip(bits(block), coordinates):
            if dot(form, z) == ((rhs ^ gauge) >> i & 1):
                allowed |= 1 << i
        fiber = affine_rows(((row, z >> j & 1) for j, row in enumerate(basis_rows)), allowed)
        if fiber is not None:
            point, directions = fiber
            yield point
            for delta in directions:
                yield point ^ delta


def moving_witness(rows, rhs, block, beta, changed):
    # BFS from a virtual pinned root reading beta; store only physical path bits.
    paths = {i: 1 << i for i in bits(beta)}
    queue = list(paths)
    for i in queue:
        for j in bits(rows[i] & block):
            if j not in paths:
                paths[j] = paths[i] | (1 << j)
                queue.append(j)
    for local in paths.values():
        if not dot(local, beta):
            continue
        for y in (0, changed):
            word = y | local
            if all(dot(rows[i], word) == (rhs >> i & 1) for i in bits(local)):
                return word
    raise ArithmeticError('two distinct local right sides failed the path theorem')


def basis(rows, rhs):
    """Return an independent list of genuine feasible words spanning all solutions."""
    rows = tuple(rows)
    n = len(rows)
    if rhs < 0 or rhs >> n or any(r < 0 or r >> n for r in rows):
        raise ValueError('invalid binary activation input')
    words = []
    for block in blocks(rows):
        changed = next((y for y in words if any(dot(rows[i], y) for i in bits(block))), 0)
        pivots = {}
        if changed:
            while len(pivots) < block.bit_count():
                _, nullspace = affine_rows(((row, 0) for row in pivots.values()), block)
                word = moving_witness(rows, rhs, block, nullspace[0], changed)
                if not insert(pivots, word & block):
                    raise ArithmeticError('nonseparating path')
                words.append(word)
        else:
            for word in fixed_generators(rows, block, rhs):
                if insert(pivots, word):
                    words.append(word)
    return words
