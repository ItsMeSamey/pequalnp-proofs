"""Find a pinned induced-even vertex set. Input JSON: {"adjacency":[...],"pins":[i,j,k]}.

Each adjacency row and the returned witness are integer bit masks in the original
vertex order. The response is {"witness":null} for NO. Use --self-test for checks.
"""
import argparse
import json
import sys
from itertools import combinations
from random import Random


def reduced(value, basis):
    while value and value.bit_length() - 1 in basis:
        value ^= basis[value.bit_length() - 1]
    return value


def basis_of(values):
    basis = {}
    for value in values:
        v = reduced(value, basis)
        if v:
            basis[v.bit_length() - 1] = v
    return basis


def kernel(rows, dimension):
    basis = basis_of(rows)
    pivots = sorted(basis.items())
    result = []
    for i in range(dimension):
        if i not in basis:
            v = 1 << i
            for j, row in pivots:
                v |= ((row & v).bit_count() % 2) << j
            result.append(v)
    return result


def apply(rows, x):
    return sum(((row & x).bit_count() % 2) << i for i, row in enumerate(rows))


def with_diagonal(rows, d):
    return [row ^ (d & (1 << i)) for i, row in enumerate(rows)]


def transpose(columns, height):
    return [sum(((col >> i) & 1) << j for j, col in enumerate(columns))
            for i in range(height)]


def fit_template(A, W, exterior, budget):
    at_site = transpose(W, len(A))
    image = transpose([apply(A, w) for w in W], len(A))
    stack = [{}]
    while stack:
        trial = stack.pop()
        b = 0
        for i in exterior:
            u = reduced(image[i], trial)
            if not u:
                continue
            v = reduced(image[i] ^ at_site[i], trial)
            if not v:
                b |= 1 << i
                continue
            if len(trial) < budget:
                for option in {u, v}:
                    stack.append({**trial, option.bit_length()-1: option})
            break
        else:
            return b
    return None


def classify(A, pins, d):
    parities = set()
    first = None
    for values in range(8):
        z = d | sum(((values >> j) & 1) << i for j, i in enumerate(pins))
        if len(basis_of(with_diagonal(A, z))) == len(A):
            parities.add(values.bit_count() % 2)
            if first is None:
                first = z
            if len(parities) == 2:
                return "both feasible", None
    if first is None:
        return "both missing", None
    # For an invertible binary matrix det(M+e_i e_i^T)=1+(M inverse)_ii.
    x = sum(int(len(basis_of(with_diagonal(A, first ^ (1 << i)))) < len(A)) << i
            for i in range(len(A)))
    assert all(x >> i & 1 for i in pins) and not x & apply(A, x)
    return "witness", x


def search_faces(A, pins, exterior, b, W):
    H = with_diagonal(A, b)
    images = [apply(H, w) for w in W]
    D = list(basis_of(images).values())
    ambient = sum(1 << i for i in exterior)
    rows = transpose(W, len(A))
    image_rows = transpose(images, len(A))
    syndrome_rows = transpose(D, len(A))

    def known(change):
        tests = (z ^ (row if change >> i & 1 else 0)
                 for i, (z, row) in enumerate(zip(image_rows, rows)))
        return len(basis_of(tests)) < len(W)

    for size in range(len(D)+1):
        for outside in combinations(exterior, size):
            maximal = ambient ^ sum(1 << i for i in outside)
            if known(maximal):
                continue
            annihilator = kernel([syndrome_rows[i] for i in outside], len(D))
            forced = 0
            for coeff in annihilator:
                forced |= apply(syndrome_rows, coeff)
            assert not forced & ~maximal
            removable = [i for i in exterior if (maximal & ~forced) >> i & 1]
            for distance in range(min(16, len(removable))+1):
                for removed in combinations(removable, distance):
                    change = maximal ^ sum(1 << i for i in removed)
                    if distance and known(change):
                        continue
                    d = b ^ change
                    status, x = classify(A, pins, d)
                    if status == "witness":
                        return status, x
                    if status == "both missing":
                        private = kernel(with_diagonal(A,d) + [1 << i for i in pins], len(A))
                        old = basis_of(W)
                        return "learn", next(w for w in private if reduced(w, old))
    return "no", None


def solve(A, pins, *, statistics=None):
    n = len(A)
    if (not isinstance(pins, (list, tuple)) or len(pins) != 3
            or any(type(i) is not int or not 0 <= i < n for i in pins) or len(set(pins)) != 3):
        raise ValueError("provide three distinct vertex indexes")
    if any(type(row) is not int or not 0 <= row < 1 << n for row in A):
        raise ValueError("invalid adjacency mask")
    for i, row in enumerate(A):
        if row >> i & 1 or any((row >> j & 1) != (A[j] >> i & 1) for j in range(i)):
            raise ValueError("adjacency must be symmetric and loopless")
    exterior = [i for i in range(n) if i not in pins]
    W = []
    budget = 0
    while True:
        b = fit_template(A, W, exterior, budget)
        if b is None:
            budget += 1
            continue
        private = kernel(with_diagonal(A, b) + [1 << i for i in pins], n)
        W = list(basis_of(W + private).values())
        if statistics is not None:
            statistics["budget"] = budget
        status, value = search_faces(A, pins, exterior, b, W)
        if status == "learn":
            W.append(value)
        else:
            return value


def self_test():
    rng = Random(54321)
    cases = [([106,21,90,85,110,81,61], [0,1,2]), ([116,56,41,86,75,71,57], [0,1,2])]
    for n in range(3,10):
        for _ in range(40):
            rows = [0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
            cases.append((rows, rng.sample(range(n),3)))
    for rows, pins in cases:
        pin_mask = sum(1 << p for p in pins)
        actual = solve(rows, pins)
        valid = {x for x in range(1 << len(rows)) if x & pin_mask == pin_mask and not x & apply(rows,x)}
        assert (actual in valid) if valid else (actual is None)
    for t in (1, 2):
        triangles = [2, 1, 0] + [0] * (3*t)
        for start in range(3, len(triangles), 3):
            for i in range(start, start+3):
                triangles[i] = (7 << start) ^ (1 << i)
        stats = {}
        assert solve(triangles, [0,1,2], statistics=stats) is None
        assert stats["budget"] == t
    for invalid in ([False,1,2], [0.0,1,2], None, [0,1,1]):
        try:
            solve([0,0,0], invalid)
        except ValueError:
            continue
        raise AssertionError("invalid pin list accepted")
    print(f"{len(cases)} original-graph checks, two budget regressions and four invalid pin cases passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    options = parser.parse_args()
    if options.self_test:
        self_test()
    else:
        if hasattr(sys, "set_int_max_str_digits"):
            sys.set_int_max_str_digits(0)
        instance = json.load(sys.stdin)
        print(json.dumps({"witness": solve(instance["adjacency"], instance["pins"])}))
