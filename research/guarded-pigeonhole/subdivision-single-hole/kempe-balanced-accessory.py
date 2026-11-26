"""Greatest Kempe-consistent subset of the mixed-six admissible language."""
from itertools import combinations, product


def orbit(word):
    names = {}
    return tuple(names.setdefault(color, len(names)) for color in word)


def pairings(positions):
    if not positions:
        yield ()
        return
    i, *remaining = positions
    for j in remaining:
        for matching in pairings([k for k in remaining if k != j]):
            yield ((i, j), *matching)


def flips(word, palette, matching):
    a, b = palette
    for selected in product((False, True), repeat=len(matching)):
        result = list(word)
        for active, ends in zip(selected, matching):
            if active:
                for i in ends:
                    result[i] = a + b - result[i]
        yield orbit(result)


def admissible_orbit(word):
    if any(word.count(c) % 2 for c in range(3)):
        return False
    return sorted(word[:3]) != sorted(word[3:]) or word == (0, 1, 2, 0, 1, 2)


def supported(word, candidates):
    for palette in combinations(range(3), 2):
        ends = [i for i, c in enumerate(word) if c in palette]
        if not any(all(w in candidates for w in flips(word, palette, match))
                   for match in pairings(ends)):
            return False
    return True


states = {orbit(w) for w in product(range(3), repeat=6)}
states = {w for w in states if admissible_orbit(w)}
while states:
    print(len(states), sorted(''.join(map(str, w)) for w in states))
    new = {w for w in states if supported(w, states)}
    if new == states:
        raise AssertionError("nonempty fixed point")
    states = new
print(0, [])
