"""Exact signed sum for disjoint matched cubic triples plus a quadratic ANF.

Uses original_dag_quadratic.gauss on each latent component assignment. A clean
edge is an isolated edge of the quadratic graph and neither endpoint may carry
a linear drift. Clean edges internal to a triple contribute a diagonal weight
without changing the component partition.
"""
from original_dag_quadratic import gauss


def clean_link_count(m, monomials):
    if m < 0:
        raise ValueError("negative triple count")
    n = 3 * m
    drift = set()
    for term in monomials:
        if term < 0 or term >> n or term.bit_count() > 2:
            raise ValueError("invalid quadratic monomial")
        drift.symmetric_difference_update((term,))

    edges = [term for term in drift if term.bit_count() == 2]
    endpoints = {}
    degree = [0] * n
    for edge in edges:
        low = edge & -edge
        pair = (low.bit_length() - 1, (edge ^ low).bit_length() - 1)
        endpoints[edge] = pair
        for vertex in pair:
            degree[vertex] += 1

    parent = list(range(m))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    linked = 0
    clean = []
    self_links = 0
    for edge, (i, j) in endpoints.items():
        if degree[i] != 1 or degree[j] != 1 or (1 << i) in drift or (1 << j) in drift:
            continue
        clean.append(edge)
        linked |= edge
        if i // 3 == j // 3:
            self_links += 1
        else:
            parent[root(i // 3)] = root(j // 3)

    groups = {}
    for block in range(m):
        groups.setdefault(root(block), []).append(block)
    representatives = list(groups)
    group_index = {key: index for index, key in enumerate(representatives)}
    edges_per_group = [0] * len(groups)
    for edge in clean:
        i, _ = endpoints[edge]
        edges_per_group[group_index[root(i // 3)]] += 1

    residual = drift.difference(clean)
    remaining = ((1 << n) - 1) ^ linked
    total = 0
    for latent in range(1 << len(groups)):
        weight = 1
        pinned = 0
        for index, key in enumerate(representatives):
            edge_count = edges_per_group[index]
            blocks = groups[key]
            if latent >> index & 1:
                weight *= (-2) ** len(blocks) * (-1) ** edge_count
                for block in blocks:
                    pinned |= 7 << (3 * block)
            else:
                weight *= 1 << edge_count
        free = remaining & ~pinned
        restricted = set()
        for term in residual:
            restricted.symmetric_difference_update((term & free,))
        total += weight * gauss(restricted, free)
    cube = 1 << n
    return {
        "signed": total,
        "ones": (cube - total) // 2,
        "zeros": (cube + total) // 2,
        "components": len(groups),
        "gauss_calls": 1 << len(groups),
        "clean_edges": len(clean),
        "self_links": self_links,
    }


def selftest():
    from itertools import combinations
    from random import Random

    def verify(m, terms):
        phase = {7 << (3 * j) for j in range(m)}
        for term in terms:
            phase.symmetric_difference_update((term,))
        raw = sum((-1) ** (sum((x & t) == t for t in phase) % 2) for x in range(1 << (3 * m)))
        result = clean_link_count(m, terms)
        assert result["signed"] == raw
        return result

    rng = Random(3591)
    for m in range(5):
        possible = [0] + [1 << i for i in range(3 * m)]
        possible.extend((1 << i) | (1 << j) for i, j in combinations(range(3 * m), 2))
        for _ in range(12):
            verify(m, [t for t in possible if rng.randrange(7) == 0])
    assert verify(1, [3, 0])["self_links"] == 1
    assert verify(1, [3, 1])["clean_edges"] == 0
    assert verify(2, [9, 17])["clean_edges"] == 0
    assert verify(2, [9, 9])["clean_edges"] == 0
    triple_parallel = verify(2, [9, 18, 36])
    assert triple_parallel["gauss_calls"] == 2 and triple_parallel["clean_edges"] == 3
    chain = [(1 << (3 * i + 1)) | (1 << (3 * i + 3)) for i in range(63)]
    result = clean_link_count(64, chain)
    # 126 endpoints removed, 66 free unpinned bits in the all-zero latent case.
    assert result["signed"] == (1 << 129) - (1 << 64)
    assert result["gauss_calls"] == 2
    print("60 seeded, five structured and one 64-block chain passed")


if __name__ == "__main__":
    selftest()
