from random import Random

from label_subset_ring import LabelRing
from punctured_witness import BinaryField


def direct(field, x, y):
    out = [0] * len(x)
    for mask in range(len(x)):
        sub = mask
        while True:
            out[mask] ^= field.mul(x[sub], y[mask ^ sub])
            if sub == 0:
                break
            sub = (sub - 1) & mask
    return tuple(out)


def check():
    rng = Random(932)
    trials = 0
    for modulus in (7, 11, 19):
        field = BinaryField(modulus)
        for h in range(7):
            ring = LabelRing(field, h)
            for _ in range(4):
                x, y = [tuple(rng.randrange(field.size) for _ in ring.zero)
                        for _ in range(2)]
                assert ring.mul(x, y) == direct(field, x, y)
                assert ring.mul(x, x) == ring.square(x)
                assert ring.mul(x, ring.one) == x
                assert ring.xor(x, x) == ring.zero
                assert ring.square((0,) + x[1:]) == ring.zero
                trials += 1
    print(trials, "random direct-convolution, unit, XOR, and square checks passed")


if __name__ == "__main__":
    check()
