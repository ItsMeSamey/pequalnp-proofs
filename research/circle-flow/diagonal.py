"""Diagonal guards for a supplied sphere rotation of the tour multigraph."""
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
from random import Random


def expand(word, rotation, diagonal, labels):
    # Occurrence i has ports 2i (incoming) and 2i+1 (outgoing).
    m = len(word)
    if not m or set(word) != set(rotation):
        raise ValueError("invalid word or rotation")
    arc_label = [0]*m
    graph = {}
    middle = {}
    weight = {}
    next_id = 4*m
    for v, order in rotation.items():
        visits = [i for i, w in enumerate(word) if v == w]
        if len(visits) != 2 or sorted(order) != [2*i+j for i in visits for j in (0, 1)]:
            raise ValueError("expected four ports at each double occurrence")
        i = visits[0]
        arc_label[i-1] ^= labels[v]
        arc_label[i] ^= labels[v]
        ring = list(order)
        role = {p: (p % 2) ^ (diagonal[v] if p//2 == i else 0) for p in ring}
        if any(role[p] == role[ring[j-1]] for j, p in enumerate(ring)):
            j = next(j for j, p in enumerate(ring)
                     if role[p] == role[ring[(j+1)%4]] == 0)
            s1, s2, t2, t1 = ring[j:] + ring[:j]
            a, b = next_id, next_id+1
            next_id += 2
            ring = [s1, a, s2, t2, b, t1]
            middle[a], middle[b] = b, a
        for j, p in enumerate(ring):
            before, after = ring[j-1], ring[(j+1)%len(ring)]
            if p in middle:
                graph[p] = [before, after, middle[p]]
            else:
                i = p//2
                wire = 2*m+2*i if p % 2 else 2*m+2*((i-1)%m)+1
                graph[p] = [before, wire, after]
    for i in range(m):
        a, b = 2*m+2*i, 2*m+2*i+1
        port, end = 2*i+1, 2*((i+1)%m)
        graph[a] = [port, b]
        graph[b] = [a, end]
        weight[port, a] = arc_label[i]
    return graph, weight


def orientation(graph):
    edges = sorted((i, j) for i, nbrs in graph.items() for j in nbrs if i < j)
    ids = {e:i for i, e in enumerate(edges)}
    seen, faces = set(), []
    for i in graph:
        for j in graph[i]:
            if (i, j) in seen:
                continue
            u, v = i, j
            row, rhs = 0, 1
            while (u, v) not in seen:
                seen.add((u, v))
                row ^= 1 << ids[tuple(sorted((u,v)))]
                rhs ^= int(u < v)
                u, v = v, graph[v][(graph[v].index(u)+1) % len(graph[v])]
            faces.append((row, rhs))
    if len(graph)-len(edges)+len(faces) != 2:
        raise ValueError("rotation is not spherical")
    basis = {}
    for row, rhs in faces[1:]:
        while row and row.bit_length() in basis:
            other, value = basis[row.bit_length()]
            row ^= other
            rhs ^= value
        if row:
            basis[row.bit_length()] = row, rhs
        else:
            assert rhs == 0
    reverse = 0
    for k, (row, rhs) in sorted(basis.items()):
        reverse |= (rhs ^ ((reverse & row).bit_count() % 2)) << (k-1)
    return {e:(-1)**((reverse >> i) & 1) for e, i in ids.items()}


def pfaffian(a):
    n = len(a)
    acc = Fraction(1)
    for i in range(0, n, 2):
        j = next((k for k in range(i+1, n) if a[i][k]), None)
        if j is None:
            return 0
        if j != i+1:
            a[j], a[i+1] = a[i+1], a[j]
            for row in a:
                row[j], row[i+1] = row[i+1], row[j]
            acc = -acc
        pivot = a[i][i+1]
        acc *= pivot
        for j in range(i+2, n):
            for k in range(j+1, n):
                a[j][k] += Fraction(a[i+1][j]*a[i][k]-a[i][j]*a[i+1][k], pivot)
                a[k][j] = -a[j][k]
    assert acc.denominator == 1
    return int(acc)


def counts(word, rotation, diagonal, labels, bits):
    if bits < 0 or any(labels[v] not in range(1 << bits) or diagonal[v] not in (0, 1)
                       for v in word):
        raise ValueError("invalid label or diagonal")
    graph, weight = expand(word, rotation, diagonal, labels)
    signs = orientation(graph)
    values = []
    for h in range(1 << bits):
        a = [[0]*len(graph) for _ in graph]
        for edge, s in signs.items():
            i, j = edge
            a[i][j] = s*(-1)**((weight.get(edge, 0) & h).bit_count() % 2)
            a[j][i] = -a[i][j]
        values.append(pfaffian(a))
    assert values[0]
    result = []
    for target in range(len(values)):
        raw = sum(v*(-1)**((target & h).bit_count()%2) for h,v in enumerate(values))
        assert raw % len(values) == 0
        result.append((1 if values[0] > 0 else -1)*raw//len(values))
    return result


def brute_matching(graph, weight, bits):
    @lru_cache(None)
    def rec(mask):
        if not mask:
            return (1,) + (0,)*((1 << bits)-1)
        i = (mask & -mask).bit_length()-1
        result = [0]*(1 << bits)
        for j in graph[i]:
            if (mask >> j) & 1:
                label = weight.get(tuple(sorted((i,j))), 0)
                for t, value in enumerate(rec(mask ^ (1 << i) ^ (1 << j))):
                    result[t ^ label] += value
        return tuple(result)
    return list(rec((1 << len(graph))-1))


def oracle(word, diagonal, labels):
    pos = {v:[i for i,w in enumerate(word) if w == v] for v in word}
    out = set()
    for flags in product(range(2), repeat=len(pos)):
        active = {v for v,b in zip(pos, flags) if b}
        label = 0
        for v in active:
            i,j = pos[v]
            if sum(w in active for w in word[i+1:j]) % 2 != diagonal[v]:
                break
            label ^= labels[v]
        else:
            out.add(label)
    return out


if __name__ == "__main__":
    rng = Random(852)
    checked = 0
    for word in ("aa","aabb","abab","abacbc","abcabc"):
        ports = {v:[2*i+j for i,w in enumerate(word) if w == v for j in (0,1)]
                 for v in sorted(set(word))}
        orders = [[(p[0],)+q for q in permutations(p[1:])] for p in ports.values()]
        planar = []
        for r in product(*orders):
            rot = dict(zip(ports,r))
            try:
                orientation(expand(word,rot,dict.fromkeys(ports,0),dict.fromkeys(ports,0))[0])
            except ValueError:
                continue
            planar.append(rot)
        assert planar
        for flags in product(range(2), repeat=len(ports)):
            d = dict(zip(ports, flags))
            labels = {v:rng.randrange(1,4) for v in ports}
            rotation = rng.choice(planar)
            result = counts(word, rotation, d, labels, 2)
            assert result == brute_matching(*expand(word, rotation, d, labels), 2)
            assert {t for t,v in enumerate(result) if v} == oracle(word,d,labels)
            checked += 1
    print(f"{checked} diagonal/word cases passed")
