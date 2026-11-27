"""Independent original-subset oracle for the six/eight-site finder."""

from itertools import combinations
from random import Random
from three_connected_odd_pair import find


def oracle(rows, p, q):
    others = [v for v in range(len(rows)) if v not in (p, q)]
    minimal = []
    result = []
    for size in range(0, len(others) + 1, 2):
        for extra in combinations(others, size):
            selected = frozenset((p, q, *extra))
            if any(old <= selected for old in minimal):
                continue
            degrees = [len(rows[v] & selected) for v in selected]
            if any(d % 2 == 0 for d in degrees):
                continue
            minimal.append(selected)
            if len(selected) < 4 or max(degrees) > 5:
                continue
            for x, y in combinations(selected, 2):
                remaining = selected - {x, y}
                reached = {min(remaining)}
                while True:
                    grown = reached | (
                        set.union(*(rows[v] for v in reached)) & remaining
                    )
                    if grown == reached:
                        break
                    reached = grown
                if reached != remaining:
                    break
            else:
                result.append(selected)
    return result


def compare(rows, p, q):
    choices = oracle(rows, p, q)
    answer = find(rows, [p, q])
    assert answer["three_connected_minimal"] == bool(choices)
    if choices:
        witness = answer["witness"]
        assert len(set(witness)) == len(witness)
        assert frozenset(witness) in choices and answer["unrestricted"] == "YES"
    else:
        assert answer["witness"] is None and answer["unrestricted"] == "UNKNOWN"
    return len(choices)


def mask_rows(masks):
    return [{i for i in range(len(masks)) if m >> i & 1} for m in masks]


def main():
    six_edges = list(combinations(range(6), 2))
    positives = 0
    for mask in range(1 << len(six_edges)):
        rows = [set() for _ in range(6)]
        for j, (a, b) in enumerate(six_edges):
            if mask >> j & 1:
                rows[a].add(b)
                rows[b].add(a)
        positives += bool(compare(rows, 0, 1))
    rng = Random(623135)
    seeds = [[52, 56, 41, 38, 35, 31], [196, 248, 185, 230, 134, 14, 11, 31]]
    for masks in seeds:
        for trial in range(100):
            seed = mask_rows(masks)
            n = len(seed)
            total = n + 4
            rows = seed + [set() for _ in range(total - n)]
            for i, j in combinations(range(total), 2):
                if j >= n and rng.randrange(2):
                    rows[i].add(j)
                    rows[j].add(i)
            perm = list(range(total))
            rng.shuffle(perm)
            renamed = [set() for _ in rows]
            for i, nei in enumerate(rows):
                renamed[perm[i]] = {perm[v] for v in nei}
            assert compare(renamed, perm[0], perm[1])
    # K3,3 is itself an odd three-connected set, but fixed same-shore pins
    # admit a smaller, not three-connected, odd support.
    bip = [set(range(3, 6)) if i < 3 else set(range(3)) for i in range(6)]
    assert not compare(bip, 0, 1)
    print(
        "32768 six-vertex graphs,",
        positives,
        "positive; 200 labelled exterior extensions; K3,3 control",
    )


if __name__ == "__main__":
    main()
