"""Check the support-section identity against original binary guards."""
from itertools import product


def apply(rows, x):
    return sum(((row & x).bit_count() % 2) << i for i, row in enumerate(rows))


def check(rows):
    cube = range(1 << len(rows))
    images = [apply(rows, x) for x in cube]
    actual = [set() for _ in cube]
    for support in cube:
        diagonal = prefix = 0
        for i in range(len(rows)):
            if not support & (1 << i):
                continue
            prefix |= 1 << i
            image = {(images[x] ^ (diagonal & x)) & prefix
                     for x in cube if not x & ~prefix}
            if len(image) != 1 << prefix.bit_count():
                diagonal |= 1 << i
        inverse = {((images[x] ^ (diagonal & x) ^ diagonal) & support): x
                   for x in cube if not x & ~support}
        assert len(inverse) == 1 << support.bit_count()
        for b in cube:
            actual[b].add(inverse[b & support])
    for b in cube:
        assert actual[b] == {x for x in cube if ((images[x] ^ b) & x) == 0}


if __name__ == '__main__':
    total = 0
    for n in range(4):
        for rows in product(range(1 << n), repeat=n):
            check(rows)
            total += 1
    print(total, 'matrices, every RHS and support')
