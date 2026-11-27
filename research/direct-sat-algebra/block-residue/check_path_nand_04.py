"""Scheduler 04 source controls for path projection and physical NAND replay."""
from itertools import combinations, product

from check_branch_nand_04 import physical_source, replay
from check_mux_single_block_04 import physical_chart
from path_kernel import path_kernel


def accepts(clauses, values):
    return all(any(values[x] ^ values[y] == d for x, y, d in clause)
               for clause in clauses)


def raw_replay(rows):
    ports, pins = physical_chart(rows)
    source = physical_source(len(rows), pins, suffix=3)

    def check(values):
        raw = [values[x] ^ offset for x, offset in ports]
        for guard in (0, 1):
            word = (*raw, guard, guard ^ 1, guard, raw[0])
            assert bool(replay(source, word)) == accepts(rows, values)

    return check


def nand_control(pin):
    rail, x, y, z = range(4)
    rows = [((x, rail, 1), (z, rail, 1)),
            ((x, rail, 0), (y, z, 1))]
    if pin is not None:
        rows.append(((z, rail, pin), (z, rail, pin)))
    kernel = path_kernel(4, rows)
    assert set(kernel.endpoints) == ({rail, y} if pin is None else {rail, y, z})
    assert len(kernel.clauses) == (0 if pin is None else 2)
    physical = raw_replay(rows)
    for bits in product((0, 1), repeat=4):
        r, a, b, c = bits
        output = 1 ^ ((a ^ r) & (b ^ r))
        assert accepts(rows, bits) == (c ^ r == output and (pin is None or pin == output))
        physical(bits)
    for bits in product((0, 1), repeat=len(kernel.endpoints)):
        retained = dict(zip(kernel.endpoints, bits))
        r, b = retained[rail], retained[y]
        expected = pin is None or ((retained[z] ^ r) == pin and (pin == 1 or b != r))
        assert accepts(kernel.clauses, retained) == expected
        full = kernel.lift(retained)
        assert (full is not None) == expected
        if full is not None:
            assert all(full[v] == bit for v, bit in retained.items())
            assert accepts(rows, full)
            physical(full)


def subdivided_clique():
    # Every K5 edge has path target one, so every original triangle is unbalanced.
    # Pair across consecutive subdivided paths, making one resource cycle.
    first, second = [], []
    for i, (a, b) in enumerate(combinations(range(5), 2), 5):
        first.append((a, i, 0))
        second.append((i, b, 1))
    rows = list(zip(second, first[1:] + first[:1]))
    kernel = path_kernel(15, rows)
    assert set(kernel.endpoints) == set(range(5)) and not kernel.clauses
    physical = raw_replay(rows)
    for bits in product((0, 1), repeat=5):
        full = kernel.lift(dict(enumerate(bits)))
        assert full is not None and tuple(full[:5]) == bits and accepts(rows, full)
        physical(full)


def main():
    for pin in (None, 0, 1):
        nand_control(pin)
    subdivided_clique()
    print("3 NAND truth-table projections and 32 subdivided K5 lifts with physical replay")


if __name__ == "__main__":
    main()
