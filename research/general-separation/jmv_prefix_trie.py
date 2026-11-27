"""Exact tiny reference. Input bit coordinates are numbered from the LSB.
Each name bit is (ordered support, integer truth table); name bits are MSB first.
The optional SAT callback receives DIMACS clauses and the declared index width.
"""


def triples(width, names, prefix, sat=None):
    if type(width) is not int or width < 0 or len(names) != 3:
        raise ValueError("invalid decoder shape")
    if type(prefix) is not int or prefix < 0 or any(len(name) < prefix for name in names):
        raise ValueError("invalid bucket width")
    bits = []
    for name in names:
        for support, table in name[:prefix]:
            if len(set(support)) != len(support) or any(
                type(i) is not int or not 0 <= i < width for i in support
            ):
                raise ValueError("invalid support")
            if type(table) is not int or table < 0 or table.bit_length() > 1 << len(support):
                raise ValueError("invalid local truth table")
            clauses = [[], []]
            for pattern in range(1 << len(support)):
                value = (table >> pattern) & 1
                clause = tuple(-(i + 1) if pattern >> j & 1 else i + 1
                               for j, i in enumerate(support))
                clauses[1 - value].append(clause)
            bits.append(clauses)
    if sat is None:
        def sat(n, clauses):
            return any(all(any(((word >> (abs(i)-1)) & 1) == (i > 0) for i in clause)
                           for clause in clauses) for word in range(1 << n))
    stack = [(0, 0, ())]
    mask = (1 << prefix) - 1
    while stack:
        depth, code, clauses = stack.pop()
        if depth == len(bits):
            yield (code >> (2 * prefix), (code >> prefix) & mask, code & mask)
            continue
        for value in (1, 0):
            candidate = clauses + tuple(bits[depth][value])
            if sat(width, candidate):
                stack.append((depth + 1, (code << 1) | value, candidate))
