"""Ordinary positive-output NAND fixtures for cyclic four-state order constraints."""


def ordered_source(n, strict_final):
    """Return (raw input count, indexed NAND pairs, positive output ID).

    Each site has two consecutive raw bits (high, low); left sites precede
    right sites. The final raw bit is the guard. strict_final=True is UNSAT.
    """
    if type(n) is not int or n < 5 or type(strict_final) is not bool:
        raise ValueError("expected at least five sites per shore and a Boolean flag")
    inputs = 4*n + 1
    guard = inputs - 1
    gates = []

    def nand(x, y):
        wire = inputs + len(gates)
        gates.append((x, y))
        return wire

    def invert(x):
        return nand(x, x)

    def both(x, y):
        return invert(nand(x, y))

    indicators = []
    for i in range(2*n):
        high, low = 2*i, 2*i+1
        highs, lows = (invert(high), high), (invert(low), low)
        indicators.append(tuple(both(highs[s >> 1], lows[s & 1]) for s in range(4)))

    tests = []

    def compare(i, j, strict):
        for s, x in enumerate(indicators[i]):
            for t, y in enumerate(indicators[j]):
                if s > t or (strict and s == t):
                    tests.append(nand(x, y))

    for i in range(n):
        for j in range(n, 2*n):
            compare(i, j, False)
    for i in range(4):
        compare(i, i+1, i < 3 or strict_final)
    for site in indicators:
        tests.extend(nand(guard, x) for x in site)
    tests.append(invert(guard))

    root = tests[0]
    for test in tests[1:]:
        root = both(root, test)
    return inputs, tuple(gates), root
