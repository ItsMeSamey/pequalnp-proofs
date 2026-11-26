"""Exact planar determinant counts for a supplied double-occurrence word."""
from collections import Counter
from itertools import product
from random import Random


def prepare(word, labels):
    positions = {}
    for i, v in enumerate(word):
        positions.setdefault(v, []).append(i)
    if not word or any(len(p) != 2 for p in positions.values()):
        raise ValueError("expected a nonempty double-occurrence word")
    adj = {v: [] for v in positions}
    for v, (i, j) in positions.items():
        for w, (k, l) in positions.items():
            if i < k < j < l or k < i < l < j:
                adj[v].append(w)
    colors = {}
    for v in positions:
        if v in colors:
            continue
        colors[v] = 0
        stack = [v]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w not in colors:
                    colors[w] = 1 - colors[u]
                    stack.append(w)
                elif colors[w] == colors[u]:
                    raise ValueError("interlacement graph is not bipartite")
    arcs = [0] * len(word)
    for v, (i, _) in positions.items():
        arcs[i-1] ^= labels[v]
        arcs[i] ^= labels[v]
    return positions, colors, arcs


def embedding(word, positions, colors):
    # Visit i has ports (4i,4i+1) and two subdivision vertices (4i+2,4i+3).
    m = len(word)
    rot = {}
    for v, (i, j) in positions.items():
        ring = [4*i, 4*i+1, 4*j, 4*j+1]
        if colors[v]:
            ring.reverse()
        for k, p in enumerate(ring):
            visit, outgoing = divmod(p, 4)
            wire = 4*visit+2 if outgoing else 4*((visit-1) % m)+3
            rot[p] = [ring[k-1], wire, ring[(k+1) % 4]]
    for i in range(m):
        rot[4*i+2] = [4*i+1, 4*i+3]
        rot[4*i+3] = [4*i+2, 4*((i+1) % m)]
    return rot


def signing(rot):
    def edge(u, v):
        return tuple(sorted((u, v)))
    edges = {edge(u, v) for u in rot for v in rot[u]}
    ids = {e: i for i, e in enumerate(sorted(edges))}
    seen = set()
    faces = []
    for u in rot:
        for v in rot[u]:
            if (u, v) in seen:
                continue
            a, b = u, v
            face = []
            while (a, b) not in seen:
                seen.add((a, b))
                face.append(ids[edge(a, b)])
                a, b = b, rot[b][(rot[b].index(a)+1) % len(rot[b])]
            faces.append(face)
    assert len(rot) - len(edges) + len(faces) == 2
    basis = {}
    for face in faces:
        row = 0
        for e in face:
            row ^= 1 << e
        rhs = (len(face)//2 + 1) % 2
        while row and row.bit_length() in basis:
            other, sign = basis[row.bit_length()]
            row ^= other
            rhs ^= sign
        if row:
            basis[row.bit_length()] = row, rhs
        else:
            assert rhs == 0
    signs = 0
    for pivot, (row, rhs) in sorted(basis.items()):
        signs |= (rhs ^ ((row & signs).bit_count() % 2)) << (pivot-1)
    return {e: (-1)**((signs >> idx) & 1) for e, idx in ids.items()}


def det(matrix):
    a = [row[:] for row in matrix]
    n = len(a)
    sign = previous = 1
    for i in range(n-1):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            sign *= -1
        for j in range(i+1, n):
            for k in range(i+1, n):
                a[j][k] = (a[j][k]*a[i][i] - a[j][i]*a[i][k]) // previous
        previous = a[i][i]
    return sign*a[-1][-1]


def counts(word, labels, bits):
    if bits < 0 or any(not 0 <= labels[v] < 1 << bits for v in word):
        raise ValueError("label outside bit width")
    pos, colors, arcs = prepare(word, labels)
    rot = embedding(word, pos, colors)
    signed = signing(rot)
    size = 2*len(word)
    values = []
    for h in range(1 << bits):
        mat = [[0]*size for _ in range(size)]
        for (a, b), s in signed.items():
            # A used wire matches its two outside edges. Its first carries the label.
            if a % 4 == 1 and b == a+1:
                s *= (-1)**((h & arcs[a//4]).bit_count() % 2)
            if a % 2:
                a, b = b, a
            mat[a//2][b//2] = s
        values.append(det(mat))
    global_sign = 1 if values[0] > 0 else -1
    result = []
    for target in range(1 << bits):
        numerator = sum(v*(-1)**((target & h).bit_count() % 2)
                        for h, v in enumerate(values))
        assert numerator % len(values) == 0
        result.append(global_sign*numerator//len(values))
    return result


def direct(word, labels, bits):
    positions, _, _ = prepare(word, labels)
    totals = Counter()
    for arc in product(range(2), repeat=len(word)):
        target, multiplicity = 0, 1
        for v, (i, j) in positions.items():
            flow = arc[i] + arc[j]
            if flow != arc[i-1] + arc[j-1]:
                break
            if arc[i-1] != arc[i]:
                target ^= labels[v]
            if flow == 2:
                multiplicity *= 2
        else:
            totals[target] += multiplicity
    return [totals[t] for t in range(1 << bits)]


def guard_support(word, labels):
    positions = {v: [i for i, w in enumerate(word) if v == w] for v in word}
    vertices = list(positions)
    support = set()
    for chosen in product(range(2), repeat=len(vertices)):
        active = {v for v, bit in zip(vertices, chosen) if bit}
        target = 0
        for v in active:
            i, j = positions[v]
            if sum(w in active for w in word[i+1:j]) % 2:
                break
            target ^= labels[v]
        else:
            support.add(target)
    return support


if __name__ == "__main__":
    rng = Random(852)
    cases = 0
    for n in range(1, 6):
        for _ in range(30):
            word = list(range(n))*2
            rng.shuffle(word)
            labels = [rng.randrange(4) for _ in range(n)]
            try:
                expected = direct(word, labels, 2)
            except ValueError:
                continue
            assert counts(word, labels, 2) == expected
            assert {t for t, c in enumerate(expected) if c} == guard_support(word, labels)
            cases += 1
    print(f"{cases} seeded bipartite words passed")
