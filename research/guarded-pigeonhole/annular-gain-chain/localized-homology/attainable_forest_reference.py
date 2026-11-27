"""Rooted routing using one full rainbow forest and span-preserving augmentation."""
from collections import deque
from itertools import product
from random import Random

from strict_forest_reference import circles, colored_path, physical, split_chords, swap


def forest_path(edges, selected, start, goal):
    adj = {}
    for j in selected:
        u, v, _, _ = edges[j]
        adj.setdefault(u, []).append((v, j))
        adj.setdefault(v, []).append((u, j))
    seen = {start: None}
    todo = [start]
    while todo:
        v = todo.pop()
        if v == goal:
            path = []
            while seen[v] is not None:
                v, e = seen[v]
                path.append(e)
            return path
        for w, j in adj.get(v, []):
            if w not in seen:
                seen[w] = (v, j)
                todo.append(w)
    return None


def augment(edges, selected):
    """Increase cardinality by one while preserving the old graphic span."""
    color_owner = {edges[j][2]: j for j in selected}
    unseen = [j for j in range(len(edges)) if j not in selected]
    by_color = {}
    for j in unseen:
        by_color.setdefault(edges[j][2], []).append(j)
    parent = {j: None for j in unseen if edges[j][2] not in color_owner}
    queue = deque(parent)
    while queue:
        j = queue.popleft()
        u, v, c, _ = edges[j]
        if j in selected:
            neighbors = by_color.get(c, [])
        else:
            neighbors = forest_path(edges, selected, u, v)
            if neighbors is None:
                enlarged = set(selected)
                while j is not None:
                    enlarged.symmetric_difference_update([j])
                    j = parent[j]
                return enlarged
        for nxt in neighbors:
            if nxt not in parent:
                parent[nxt] = j
                queue.append(nxt)
    return None


def solve(p, gates, s, t):
    """Return (reference_found, physical_join_mask_or_None)."""
    chords = split_chords(p, gates)
    if chords is None:
        return False, None
    b = swap(p, chords)
    labels = {a: i for i, w in enumerate(circles(b)) for a in w}
    edges = []
    for c, triple in enumerate(gates):
        for on in (False, True):
            target = [p[triple[(j + int(on)) % 3]] for j in range(3)]
            u, v = [x for x, y in zip(triple, target) if b[x] != y]
            edges.append((labels[u], labels[v], c, on))
    path = colored_path(edges, labels[s], labels[t])
    if path is None:
        return True, None
    selected = {2*c + int(opt) for c, opt in path}
    while len(selected) < len(gates):
        new = augment(edges, selected)
        assert new is not None
        selected = new
    mask = [False] * len(gates)
    for j in selected:
        _, _, c, on = edges[j]
        mask[c] = on
    assert any(s in w and t in w for w in circles(physical(p, gates, mask)))
    return True, mask


def check_augmentation():
    rng = Random(739)
    for _ in range(350):
        n = rng.randrange(1, 7)
        edges = [(rng.randrange(5), rng.randrange(5), rng.randrange(5), i) for i in range(n)]
        valid = []
        for mask in range(1 << n):
            used = set()
            colors = set()
            for j, (u, v, c, _) in enumerate(edges):
                if not mask & (1 << j):
                    continue
                if c in colors or forest_path(edges, used, u, v) is not None:
                    break
                used.add(j)
                colors.add(c)
            else:
                valid.append(used)
        largest = max(map(len, valid))
        for old in valid:
            new = augment(edges, old)
            assert (new is None) == (len(old) == largest)
            if new is not None:
                assert new in valid and len(new) == len(old) + 1
                assert all(forest_path(edges, new, *edges[j][:2]) is not None for j in old)


if __name__ == "__main__":
    check_augmentation()
    rng = Random(1950)
    accepted = positive = 0
    for n in range(1, 7):
        gates = [tuple(range(3*i, 3*i+3)) for i in range(n)]
        for _ in range(250):
            p = list(range(3*n))
            rng.shuffle(p)
            s, t = rng.sample(range(len(p)), 2)
            ok, answer = solve(p, gates, s, t)
            if ok:
                accepted += 1
                expected = any(any(s in w and t in w for w in circles(physical(p, gates, bits)))
                               for bits in product((False, True), repeat=n))
                assert expected == (answer is not None)
                positive += expected
    print(f"350 rainbow-forest families and 1500 native instances; {accepted} accepted, {positive} YES.")
