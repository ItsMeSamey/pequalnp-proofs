"""One-sided randomized witness search on circle graphs given a chord word.

Each vertex is an integer from 0 to n-1 occurring exactly twice in word.
Marks are degree parities. Nonnegative integers encode binary-vector labels.
A returned set is verified. None may be a false negative with probability
at most 4**(-trials), using independent uniform field samples.
"""

from math import isqrt
from random import SystemRandom


def _field_prime(order):
    candidate = max(5, 2 * order + 1)
    while any(candidate % divisor == 0 for divisor in range(3, isqrt(candidate) + 1, 2)):
        candidate += 2
    return candidate


def _pfaffian(matrix, prime):
    """Evaluate the Pfaffian in place by skew Gaussian elimination."""
    size = len(matrix)
    if size % 2:
        return 0
    value = 1
    for i in range(0, size, 2):
        pivot_column = next((j for j in range(i + 1, size) if matrix[i][j]), None)
        if pivot_column is None:
            return 0
        j = i + 1
        if j != pivot_column:
            matrix[j], matrix[pivot_column] = matrix[pivot_column], matrix[j]
            for row in matrix:
                row[j], row[pivot_column] = row[pivot_column], row[j]
            value = -value
        pivot = matrix[i][j]
        value = value * pivot % prime
        inverse = pow(pivot, -1, prime)
        for x in range(j + 1, size):
            left = matrix[i][x] * inverse % prime
            right = matrix[j][x] * inverse % prime
            for y in range(x + 1, size):
                entry = (matrix[x][y] - left * matrix[j][y] + right * matrix[i][y]) % prime
                matrix[x][y] = entry
                matrix[y][x] = -entry % prime
    return value


def _gadget(word, marks, labels):
    n = len(marks)
    arc_labels = [0] * len(word)
    signs = []
    seen = set()
    for j, vertex in enumerate(word):
        sign = -1 if vertex in seen and marks[vertex] else 1
        signs.extend((-sign, sign))
        if vertex not in seen:
            arc_labels[j - 1] ^= labels[vertex]
            arc_labels[j] ^= labels[vertex]
            seen.add(vertex)
    edges = []
    next_vertex = 6 * n
    offset = 0
    for j, label in enumerate(arc_labels):
        outgoing = 2 * j + 1
        incoming = 2 * ((j + 1) % len(word))
        for token in (outgoing, incoming):
            chord = word[token // 2]
            coefficient = label if token == outgoing else 0
            anchor = 4 * n + 2 * chord
            edges.extend(((token, anchor, coefficient), (token, anchor + 1, coefficient)))
        if signs[outgoing] < 0:
            offset ^= label
        if signs[outgoing] == signs[incoming]:
            edges.append((outgoing, incoming, 0))
        else:
            edges.extend(((outgoing, next_vertex, 0), (incoming, next_vertex, 0)))
            next_vertex += 1
    return next_vertex, edges, signs, offset


def _filtered(vertices, edges, weights, target, group_size, prime):
    """The unnormalized Walsh coefficient at target for one field assignment."""
    if not vertices:
        return group_size % prime if target == 0 else 0
    index = {v: i for i, v in enumerate(vertices)}
    active = [(index[u], index[v], label, weight) for (u, v, label), weight in zip(edges, weights)
              if u in index and v in index]
    result = 0
    for character in range(group_size):
        matrix = [[0] * len(vertices) for _ in vertices]
        for i, j, label, weight in active:
            if i > j:
                i, j = j, i
            entry = -weight if (label & character).bit_count() % 2 else weight
            matrix[i][j] = entry % prime
            matrix[j][i] = -entry % prime
        p = _pfaffian(matrix, prime)
        result += -p if (target & character).bit_count() % 2 else p
    return result % prime


def _matching(order, edges, target, group_size, prime, rng):
    vertices = list(range(order))
    weights = [rng.randrange(prime) for _ in edges]
    if not _filtered(vertices, edges, weights, target, group_size, prime):
        return None
    partner = {}
    while vertices:
        u = vertices[0]
        for (left, right, label), weight in zip(edges, weights):
            if not weight or u not in (left, right):
                continue
            v = right if u == left else left
            if v in partner:
                continue
            remaining = [x for x in vertices if x != u and x != v]
            if _filtered(remaining, edges, weights, target ^ label, group_size, prime):
                partner[u], partner[v] = v, u
                target ^= label
                vertices = remaining
                break
        else:
            raise AssertionError("Pfaffian expansion lost its nonzero term")
    return partner


def _verify(selected, visits, marks, labels, target):
    value = 0
    for v in selected:
        value ^= labels[v]
        start, end = visits[v]
        crossing = sum((start < visits[w][0] < end) ^ (start < visits[w][1] < end)
                       for w in selected)
        if crossing % 2 != marks[v]:
            return False
    return value == target


def find_circle_parity_witness(word, marks, labels, target, *, trials=8, rng=None):
    """Return a verified set, or None on a negative outcome."""
    n = len(marks)
    if len(labels) != n or len(word) != 2 * n or trials < 1:
        raise ValueError("inconsistent sizes or nonpositive trial count")
    if target < 0 or any(v < 0 for v in labels) or any(a not in (0, 1) for a in marks):
        raise ValueError("labels must be nonnegative and marks must be binary")
    visits = [[] for _ in range(n)]
    for j, v in enumerate(word):
        if not 0 <= v < n:
            raise ValueError("word contains an unknown vertex")
        visits[v].append(j)
    if any(len(pair) != 2 for pair in visits):
        raise ValueError("every vertex must occur twice")
    if not target:
        return set()
    if not n:
        return None
    order, edges, signs, offset = _gadget(word, marks, labels)
    if order % 2:
        return None
    group_size = 1 << max([target] + list(labels)).bit_length()
    prime = _field_prime(order)
    rng = SystemRandom() if rng is None else rng
    for _ in range(trials):
        partners = _matching(order, edges, target ^ offset, group_size, prime, rng)
        if partners is None:
            continue
        arc_bits = []
        for j,v in enumerate(word):
            outgoing = 2 * j + 1
            normalized = partners[outgoing] in (4*n + 2*v, 4*n + 2*v + 1)
            arc_bits.append(normalized ^ (signs[outgoing] < 0))
        selected = {v for v, pair in enumerate(visits) if arc_bits[pair[0]-1] != arc_bits[pair[0]]}
        if not _verify(selected, visits, marks, labels, target):
            raise AssertionError("matching did not yield a valid graph witness")
        return selected
    return None
