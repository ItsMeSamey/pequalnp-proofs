"""Exhaust ordinary quadratic PC in the abstract unary convolution lemma."""
from itertools import combinations, product


def multiply(left, right):
    out = set()
    for a in left:
        for b in right:
            term = a | b
            if term in out:
                out.remove(term)
            else:
                out.add(term)
    return out


def indicator(linear, bit):
    return linear ^ ({0} if bit == 0 else set())


def records(table, index, weight):
    out = []
    for i, allowed in enumerate(table):
        atom = indicator(index, i)
        if not allowed:
            out.append(atom)
        elif len(allowed) == 1:
            value, = allowed
            out.append(multiply(atom, weight ^ ({0} if value else set())))
    return out


def closure(lines, n=4):
    masks = [sum(1 << i for i in bits) for d in range(3)
             for bits in combinations(range(n), d)]
    ids = {mask: i for i, mask in enumerate(masks)}
    def encode(poly):
        return sum(1 << ids[mask] for mask in poly)
    basis = {}
    def reduce(p):
        while p and p.bit_length() in basis:
            p ^= basis[p.bit_length()]
        return p
    queue = [encode(f) for f in lines]
    while queue:
        p = reduce(queue.pop())
        if not p:
            continue
        basis[p.bit_length()] = p
        if p.bit_length() <= n + 1:
            polynomial = {m for i, m in enumerate(masks) if p >> i & 1}
            queue.extend(encode(multiply(polynomial, {1 << i})) for i in range(n))
    return lambda poly: not reduce(encode(poly))


def main():
    choices = [set(), {0}, {1}, {0,1}]
    count = certified = 0
    for a0, a1, b0, b1 in product(choices, repeat=4):
        f, g = (a0,a1), (b0,b1)
        derived = closure(records(f, {1}, {4}) + records(g, {2}, {8}))
        target = [{p ^ q for a in (0,1) for p in f[a] for q in g[a ^ h]}
                  for h in (0,1)]
        for rec in records(target, {1,2}, {4,8}):
            assert derived(rec)
            certified += 1
        count += 1
    print(f'{count} arbitrary unary pairs, {certified} parent records verified in degree two.')


if __name__ == '__main__':
    main()
