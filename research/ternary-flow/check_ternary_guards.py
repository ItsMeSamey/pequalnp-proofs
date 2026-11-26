"""Exhaust all sound one-hot pivot-mask signatures at a ternary flow vertex."""
from itertools import combinations, product


def main():
    words = list(product(range(3), repeat=3))
    bits = [sum(1 << (3 * p + x) for p, x in enumerate(w)) for w in words]
    for charge in range(3):
        legal = sum(1 << i for i, w in enumerate(words) if sum(w) % 3 == charge)
        illegal = ((1 << len(words)) - 1) ^ legal
        by_pivot = []
        for pivot in range(9):
            signatures = set()
            for mask in range(1 << 9):
                for bias in (0, 1):
                    signature = sum(1 << i for i, x in enumerate(bits)
                                    if x >> pivot & 1 and
                                    ((x & mask).bit_count() + bias) % 2)
                    if signature and not signature & legal:
                        signatures.add(signature)
            assert len(signatures) == 3 and all(s.bit_count() == 4 for s in signatures)
            by_pivot.append(signatures)
        for count, expected in ((5, 0), (6, 603)):
            covers = 0
            for subset in combinations(by_pivot, count):
                for choice in product(*subset):
                    seen = 0
                    for s in choice:
                        seen |= s
                    covers += seen == illegal
            assert covers == expected
        for i, (a, b, c) in enumerate(words):
            c = (c - charge) % 3
            working = ((a == b) == (a == c)) and ((b == a) == (b == c))
            assert working == bool(legal >> i & 1)
    print('All three charges: 3 useful signatures per pivot, 0 five-row covers, '
          '603 six-row covers; six-row gadget verified.')


if __name__ == '__main__':
    main()
