from random import Random
from forest import forest_possible


def values(guards, labels):
    valid = set()
    for word in range(1 << len(guards)):
        if all(not (word >> i & 1) or any(c ^ ((word & d).bit_count() % 2)
               for c, d in row) for i, row in enumerate(guards)):
            result = 0
            for i, label in enumerate(labels):
                if word >> i & 1:
                    result ^= label
            valid.add(result)
    return valid


rng = Random(3519)
for _ in range(600):
    n = rng.randrange(11)
    pred = [0] * n
    for j in range(n - 1):
        i = rng.randrange(j + 1, n + 1)
        if i < n:
            pred[i] |= 1 << j
    guards = [[(rng.randrange(2), rng.getrandbits(n) & d) for _ in range(rng.randrange(5))]
              for d in pred]
    labels = [rng.randrange(8) for _ in guards]
    expected = values(guards, labels)
    assert expected == {h for h in range(8) if forest_possible(guards, labels, h)}
print("600 forests / 4,800 marker targets passed")
