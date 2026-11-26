"""Concrete universal selector coverage check with the same polynomial-basis field implementation."""
from itertools import product
from prg.viola import block, field_modulus


def check(lengths):
    total = sum(lengths)
    bits = (total - 1).bit_length() + len(lengths) + 1
    modulus = field_modulus(bits)
    q = 1 << bits
    selectors = {block(total, alpha, gamma, modulus) for alpha in range(q) for gamma in range(q)}
    positions = []
    start = 0
    for length in lengths:
        positions.append([x << start for x in range(1, 1 << length)])
        start += length
    cases = 0
    for true_masks in product(*positions):
        assert any(all((s & chosen).bit_count() % 2 for chosen in true_masks) for s in selectors)
        cases += 1
    return (lengths, len(selectors), cases)


if __name__ == '__main__':
    for lengths in ((3,), (2,2), (2,2,1), (1,3,2), (12,)):
        print(check(lengths))
