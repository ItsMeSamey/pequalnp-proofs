"""Bounded exhaustive original NAND oracle for the scheduler 04 branch checks."""
from itertools import product

from balanced_block import UnsupportedBlock, balanced_block_witness
from branch_block import branch_block_witness
from matching_nand import compile_source


def physical_source(shells, pins, suffix):
    # Each shell is one matching edge on fresh two-bit color endpoints.
    bridges = [(2 * j, 2 * j + 1) for j in range(shells)]
    inputs, body, output = compile_source(2 * shells, [], bridges, suffix)
    gates = list(body)

    def nand(left, right):
        gates.append((left, right))
        return inputs + len(gates) - 1

    for left, right, difference in pins:
        shared = nand(left, right)
        unequal = nand(nand(left, shared), nand(right, shared))
        pin = unequal if difference else nand(unequal, unequal)
        combined = nand(output, pin)
        output = nand(combined, combined)
    return inputs, gates, output


def replay(source, word):
    inputs, gates, output = source
    assert len(word) == inputs and all(bit in (0, 1) for bit in word)
    wires = list(word)
    for left, right in gates:
        assert 0 <= left < len(wires) and 0 <= right < len(wires)
        wires.append(1 - (wires[left] & wires[right]))
    return wires[output]


def audit(signs, expected):
    # Two shells share precisely two potential classes. Raw endpoint order is
    # (p,p,q^a,q^b) for each shell; 0 and 2 are the p and q representatives.
    assert signs[0] == 0
    pins = [(0, 1, 0), (0, 4, 0), (0, 5, 0),
            (2, 3, signs[1]), (2, 6, signs[2]), (2, 7, signs[3])]
    try:
        balanced_block_witness(2, pins)
    except UnsupportedBlock:
        pass
    else:
        raise AssertionError("expected a nonsimple unbalanced parallel block")

    result = branch_block_witness(2, pins)
    source = physical_source(2, pins, suffix=3)
    accepted = sum(replay(source, word) for word in product((0, 1), repeat=source[0]))
    assert accepted == expected and (result is not None) == bool(accepted)
    if result is not None:
        # Original physical layout is eight color bits, guard t, then y0,y1,y2.
        # Both choices of t lift. Check the source's low-coordinate suffix tie.
        for guard in (0, 1):
            word = (*result, guard, 1 ^ guard, guard, result[0])
            assert replay(source, word)
            assert not replay(source, (*word[:-1], 1 ^ word[-1]))


def main():
    audit((0, 0, 1, 1), 0)
    audit((0, 0, 1, 0), 4)
    audit((0, 1, 1, 0), 8)
    print("3 signed-pin branch fixtures, 12288 physical NAND words, SAT lifts and NO")


if __name__ == "__main__":
    main()
