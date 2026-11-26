"""Exhaustive witness checks on seeded small instances; integers encode bit vectors."""
from itertools import product
from random import Random


def parity(value):
    return value.bit_count() % 2


def truth(literal, value):
    mask, bias = literal
    return parity(mask & value) ^ bias


def compile_native(guards, terminals, observed_count):
    # Variables are ordered hidden then observed. Keep observations as parameters.
    hidden_count = len(guards)
    blocks = []
    own = []
    literals = []
    for index, clause in enumerate(guards + terminals):
        start = len(literals)
        literals.extend(clause)
        own.extend([index if index < hidden_count else None] * len(clause))
        blocks.append(((1 << len(clause)) - 1) << start)
    n = len(literals)
    columns = [0] * n
    target = 0
    observed_columns = [0] * observed_count
    for row, ((mask, bias), index) in enumerate(zip(literals, own)):
        if index is not None and (mask >> index) & 1:
            mask ^= 1 << index
            bias ^= 1
        target |= (1 ^ bias) << row
        for hidden, block in enumerate(blocks[:hidden_count]):
            if (mask >> hidden) & 1:
                for col in range(n):
                    if (block >> col) & 1:
                        columns[col] ^= 1 << row
        for col in range(observed_count):
            if (mask >> (hidden_count + col)) & 1:
                observed_columns[col] ^= 1 << row
    for j, block in enumerate(blocks[hidden_count:]):
        target ^= 1 << (n+j)
        for col in range(n):
            if (block >> col) & 1:
                columns[col] ^= 1 << (n+j)
    return blocks[:hidden_count], columns, target, observed_columns


def normalized(groups, target, width, chosen):
    # Binary elimination, carrying coordinates in the extending basis.
    pivots = {}
    def reduce(v):
        coords = 0
        for j in sorted(pivots, reverse=True):
            if v >> j & 1:
                delta, label = pivots[j]
                v ^= delta
                coords ^= label
        return v, coords
    basis = [pair[c] for pair, c in zip(groups, chosen)]
    for v in basis + [1 << i for i in range(width)]:
        rem, coords = reduce(v)
        if rem:
            pivots[rem.bit_length()-1] = rem, coords ^ (1 << len(pivots))
    assert len(pivots) == width
    assert [reduce(v)[1] for v in basis] == [1 << i for i in range(len(groups))]
    return [reduce(pair[1-c])[1] for pair, c in zip(groups, chosen)], reduce(target)[1]


def witnesses(columns, target):
    n = len(columns)
    for y in range(1 << n):
        slack = target
        for i, col in enumerate(columns):
            if y >> i & 1:
                slack ^= col
        if slack >> n == 0 and not (slack & y):
            yield y, slack


def test_native(rng):
    checks = 0
    for _ in range(500):
        h, o = rng.randrange(4), rng.randrange(3)
        def clause():
            return [(rng.randrange(1 << (h+o)), rng.randrange(2)) for _ in range(rng.randrange(3))]
        guards = [clause() for _ in range(h)]
        terminals = [clause() for _ in range(rng.randrange(3))]
        blocks, cols, base, obscols = compile_native(guards, terminals, o)
        for obs in range(1 << o):
            target = base
            for j, col in enumerate(obscols):
                if obs >> j & 1:
                    target ^= col
            decoded = {sum(parity(y & block) << i for i, block in enumerate(blocks))
                       for y, _ in witnesses(cols, target)}
            original = set()
            for z in range(1 << h):
                v = z | (obs << h)
                if (all(not(z >> i & 1) or any(truth(g,v) for g in clause)
                        for i,clause in enumerate(guards)) and
                    all(any(truth(g,v) for g in clause) for clause in terminals)):
                    original.add(z)
            assert decoded == original
            checks += 1
    return checks


def test_basis(rng):
    checks = 0
    for _ in range(350):
        n = rng.randrange(1,7)
        width = rng.randrange(n, 2*n+1)
        # Random invertible coordinate scrambling via transvections.
        basis = [1 << j for j in range(width)]
        for _ in range(4*width):
            a,b = rng.randrange(width),rng.randrange(width)
            if a != b:
                basis[a] ^= basis[b]
        chosen = [rng.randrange(2) for _ in range(n)]
        groups = []
        for i,c in enumerate(chosen):
            pair = [basis[i], rng.randrange(1 << width)]
            groups.append(pair[::-1] if c else pair)
        target = rng.randrange(1 << width)
        columns,t = normalized(groups,target,width,chosen)
        native = {tuple(1+(1-c) if y >> i & 1 else 1+c if u >> i & 1 else 0
                        for i,c in enumerate(chosen)) for y,u in witnesses(columns,t)}
        brute = set()
        for choices in product(range(3), repeat=n):
            value = 0
            for j, choice in enumerate(choices):
                if choice:
                    value ^= groups[j][choice-1]
            if value == target:
                brute.add(choices)
        assert native == brute
        checks += 1
    return checks


if __name__ == '__main__':
    rng = Random(37819)
    print(test_native(rng), 'projected native observation checks')
    print(test_basis(rng), 'scrambled basis witness-set checks')
