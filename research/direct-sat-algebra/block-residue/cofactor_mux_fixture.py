"""Original mux arrays for independently checking both shared-pilot cofactors."""
from itertools import product

from corridor_nand import _replay


def mux_array(m, contradiction=False):
    if type(m) is not int or m < 2:
        raise ValueError("expected at least two muxes")
    inputs = 2 * m + 1
    gates = []

    def nand(a, b):
        gates.append((a, b))
        return inputs + len(gates) - 1

    pilot = 0
    opposite = nand(pilot, pilot)

    def mux(x, y):
        return nand(nand(pilot, x), nand(opposite, y))

    selected = [mux(1 + i, 1 + m + i) for i in range(m)]
    if contradiction:
        x, y = 1, 1 + m
        selected.insert(1, mux(nand(x, x), nand(y, y)))
    out = selected[0]
    for v in selected[1:]:
        inverted = nand(out, v)
        out = nand(inverted, inverted)
    return inputs, tuple(gates), out


def audit_original(m, contradiction):
    inputs, gates, out = mux_array(m, contradiction)
    assert len(gates) == 5 * m + (6 if contradiction else -1)
    totals = [0, 0]
    for raw in product((0, 1), repeat=inputs):
        actual = _replay(raw, gates)[out]
        selected = raw[1:1+m] if raw[0] else raw[1+m:]
        assert actual == (not contradiction and all(selected))
        totals[raw[0]] += actual
    assert totals == ([0, 0] if contradiction else [1 << m, 1 << m])


def main():
    for m in (3, 4):
        for contradiction in (False, True):
            audit_original(m, contradiction)
    print("1280 original mux-array input words; both pilot fibers on four netlists")


if __name__ == "__main__":
    main()
