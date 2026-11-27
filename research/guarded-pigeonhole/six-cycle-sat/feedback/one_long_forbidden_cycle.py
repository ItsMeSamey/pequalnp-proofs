"""Normalize a closed native network. Wires are named by their incoming sockets."""
from itertools import permutations
from random import Random


def cycles(perm):
    seen = set()
    result = []
    for start in range(len(perm)):
        if start in seen:
            continue
        orbit = []
        v = start
        while v not in seen:
            orbit.append(v)
            seen.add(v)
            v = perm[v]
        result.append(orbit)
    return result


def forbidden(sigma):
    return [sigma[i-i%3+(i-1)%3] for i in range(len(sigma))]


def normalize(sigma):
    """Return normalized off-output permutation, preserving original wire names."""
    n = len(sigma)
    if n%3 or sorted(sigma) != list(range(n)):
        raise ValueError("expected a permutation in triples")
    out = list(sigma)
    pred = [0]*n
    for i, v in enumerate(out):
        pred[v] = i
    reps = [orbit[0] for orbit in cycles(forbidden(out))]
    for b in reps[1:]:
        a = reps[0]
        j = len(out)
        u, v = pred[a], pred[b]
        out[u], out[v] = j, j+1
        out.extend([a, j+2, b])
        pred[a], pred[b] = j, j+2
        pred.extend([u, v, j+1])
    return out


def orbits(sigma, mask, original_size):
    perm = [sigma[i-i%3+(i%3+((mask>>(i//3))&1))%3] for i in range(len(sigma))]
    return sorted(tuple(v for v in orbit if v < original_size) for orbit in cycles(perm))


if __name__ == "__main__":
    rng = Random(20261127)
    cases = list(permutations(range(3))) + list(permutations(range(6)))
    for _ in range(100):
        cases.append(rng.sample(range(9), 9))
    comparisons = 0
    for sigma in cases:
        n = len(sigma)
        out = normalize(sigma)
        old = cycles(forbidden(sigma))
        added = len(old)-1
        lengths = sorted(map(len, cycles(forbidden(out))))
        if lengths != [1]*added+[n+2*added]:
            raise AssertionError((sigma, lengths))
        for mask in range(1<<(n//3)):
            reference = orbits(sigma, mask, n)
            for extra in range(1<<added):
                if orbits(out, mask | (extra<<(n//3)), n) != reference:
                    raise AssertionError((sigma, mask, extra))
                comparisons += 1
    print(len(cases), "networks,", comparisons, "physical mask lifts")
