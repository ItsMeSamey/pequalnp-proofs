"""Original compiled NAND truth tables and witness replay for the total solver."""
from itertools import product

from biclique_physical import UnsupportedConflict, biclique_block_witness
from biclique_total import total_block_witness
from check_branch_nand_04 import physical_source, replay
from check_mux_single_block_04 import physical_chart


def truth_count(source):
    # Bit k is the gate value on physical input word k. Evaluate the complete
    # netlist on all words at once, including both guard and suffix failures.
    inputs, gates, output = source
    rows = 1 << inputs
    domain = (1 << rows) - 1
    wires = []
    for bit in range(inputs):
        width = 1 << bit
        low = (1 << width) - 1
        repeats = domain // ((1 << (2 * width)) - 1)
        wires.append((low << width) * repeats)
    for x, y in gates:
        wires.append(domain ^ (wires[x] & wires[y]))
    return wires[output].bit_count()


def check(shells, pins, expected, fallback=False):
    source = physical_source(shells, pins, suffix=3)
    assert source[0] == 4 * shells + 4
    assert truth_count(source) == expected
    if fallback:
        try:
            biclique_block_witness(shells, pins)
        except UnsupportedConflict:
            pass
        else:
            raise AssertionError("expected the grouped path to reject the induced P4")
    model = total_block_witness(shells, pins)
    assert (model is not None) == bool(expected)
    if model is not None:
        for guard, first, second, tied in product((0, 1), repeat=4):
            word = (*model, guard, first, second, tied)
            assert bool(replay(source, word)) == (
                first != second and second == guard and tied == model[0])


def main():
    for signs, expected in [((0, 0, 1, 1), 0),
                            ((0, 0, 1, 0), 4),
                            ((0, 1, 1, 0), 8)]:
        pins = [(0, 1, 0), (0, 4, 0), (0, 5, 0),
                (2, 3, signs[1]), (2, 6, signs[2]), (2, 7, signs[3])]
        check(2, pins, expected)
    # Distinct signed loops have constant truth but remain four distinct atoms.
    # Their three physical pairs form A--B--C--D. In the NO instance the middle
    # shell fails for every raw assignment consistent with the copy pins.
    for signs, expected in [((0, 1, 0, 1), 32), ((0, 1, 1, 0), 0)]:
        atoms = [(i, i, s) for i, s in enumerate(signs)]
        _, pins = physical_chart(list(zip(atoms, atoms[1:])))
        check(3, pins, expected, fallback=True)
    print("5 compiled NAND truth tables: 143360 physical words, P4 YES/NO, guard/suffix replay")


if __name__ == "__main__":
    main()
