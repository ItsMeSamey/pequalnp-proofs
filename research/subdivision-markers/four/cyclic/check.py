"""Exhaustive observation/hidden enumeration for small cyclic native gadgets."""
from itertools import product


def inspect(x, rings, length, omitted=None):
    outputs = set()
    for assignment in range(1 << (rings * length)):
        out = 0
        for i,j in product(range(rings),range(length)):
            v = (assignment >> (i*length+j)) & 1
            prev = (assignment >> (i*length+(j-1)%length)) & 1
            g = prev ^ (((x >> i) & 1) if j == 0 else 0)
            if v and not g and (i,j) != omitted:
                break
            if j == 0:
                out |= (v ^ prev) << i
        else:
            outputs.add(out)
    return outputs


if __name__ == '__main__':
    instances = [(r,l) for r in range(1,5) for l in range(2,9) if r*l <= 12]
    inputs = removals = 0
    for r,l in instances:
        for x in range(1 << r):
            ys = inspect(x,r,l)
            assert ys == {y for y in range(1 << r) if y & ~x == 0}
            assert any(y.bit_count() % 2 for y in ys) == bool(x)
            assert (((1 << r) - 1) in ys) == (x == (1 << r)-1)
            inputs += 1
        for cut in product(range(r),range(l)):
            assert any(y.bit_count() % 2 for y in inspect(0,r,l,cut))
            removals += 1
    print(f'{len(instances)} ring systems, {inputs} observed inputs, {removals} single-guard removals passed')
