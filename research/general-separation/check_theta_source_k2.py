"""Source-only control on the 52 labelled edges of the expanded theta graph."""
from collections import defaultdict
from itertools import combinations

from ring_image_affine_demands import decide_source


def main():
    t = 8
    incident = defaultdict(list)
    edges = []

    def edge(u, v):
        edges.append((u, v))
        label = len(edges)
        incident[u].append(label)
        incident[v].append(label)
        return label

    chains = []
    for side in ("left", "right"):
        chains.append([edge((side, i), (side, i+1)) for i in range(2*t-2)])
    paths = []
    for j in range(t):
        a, b = ("a", j), ("b", j)
        paths.append((edge(("left", 2*j), a), edge(a, b), edge(b, ("right", 2*j))))
    stars = list(incident.values())
    conflicts = [(-i, -j) for star in stars for i, j in combinations(star, 2)]
    demands = [[e for j, (left, _, right) in enumerate(paths)
                if ((j//2) & v).bit_count() % 2 == 0 for e in (left, right)]
               for v in (1, 2, 3)]
    rows = stars + conflicts + demands
    assert (len(edges), len(stars), len(conflicts), len(rows)) == (52, 46, 70, 119)

    words, labels = [], []
    for j in range(t):
        selected = {middle for i, (_, middle, _) in enumerate(paths) if i != j}
        selected.update((paths[j][0], paths[j][2]))
        # Removing the externally matched port leaves two even chains.
        for chain in chains:
            selected.update(chain[:2*j:2])
            selected.update(chain[2*j+1::2])
        word = tuple(int(i in selected) for i in range(1, len(edges)+1))
        assert all(len(selected.intersection(star)) == 1 for star in stars)
        words.append(word)
        labels.append(tuple(bool(selected.intersection(d)) for d in demands))
    assert len(set(words)) == 8
    functions = list(zip(*labels))
    assert len(set(functions)) == 3
    assert all(tuple(f) == tuple(not (((j//2) & v).bit_count() % 2)
                                 for j in range(t)) for v, f in zip((1,2,3), functions))
    expected = {w for w, hits in zip(words, labels) if all(hits)}
    assert len(expected) == 2

    result = decide_source(len(edges), rows)
    assert result["status"] == "nonzero" and result["count"] == len(expected)
    assert (result["affine_rank"], result["affine_count"], result["nonaffine_count"]) == (2,3,0)
    witness = tuple(result["assignment"])
    assert witness in expected
    assert all(any(witness[abs(lit)-1] == (lit > 0) for lit in row) for row in rows)
    print("52 edges, 119 original clauses, eight matchings, three affine hits, rank two, two witnesses")


if __name__ == "__main__":
    main()
