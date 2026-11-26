"""Compare the first-violation recursion with exhaustive counting."""
from random import Random


def models(cubes, n, mask, value):
    return sum(assignment & mask == value and
               all(assignment & scope != bits for scope, bits in cubes)
               for assignment in range(1 << n))


def peel(n, cubes, k, pinned=0, value=0):
    consistent = [(scope & ~pinned, bits & ~pinned) for scope, bits in cubes
                  if not ((value ^ bits) & scope & pinned)]
    short = [cube for cube in consistent if cube[0].bit_count() <= k]
    long = [cube for cube in consistent if cube[0].bit_count() > k]
    result = models(short, n, pinned, value)
    for j, (scope, bits) in enumerate(long):
        result -= peel(n, short + long[:j], k, pinned | scope, value | bits)
    return result


rng = Random(465874)
for trial in range(600):
    n = rng.randrange(1, 10)
    cubes = []
    for _ in range(rng.randrange(12)):
        mask = rng.randrange(1 << n)
        cubes.append((mask, rng.randrange(1 << n) & mask))
    cubes.sort(key=lambda cube: cube[0].bit_count())
    assert peel(n, cubes, rng.randrange(4)) == models(cubes, n, 0, 0)
print("600 first-violation recursions matched exhaustive counts.")
