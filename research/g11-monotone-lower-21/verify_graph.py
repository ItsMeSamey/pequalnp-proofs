from itertools import combinations

edges = {(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
         (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
         (7, 9), (8, 9)}
core_labels = [8, 9, 5, 4, 1, 0, 2, 10]
core_minterms = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5),
                 (2, 6), (3, 4), (3, 7), (5, 7), (6, 7)]
core = {tuple(sorted((core_labels[i], core_labels[j]))) for i, j in core_minterms}
assert core == {e for e in edges if set(e).isdisjoint({3, 6, 7})}
neighbors = [{b if a == v else a for a, b in edges if v in (a, b)} for v in range(11)]
assert neighbors[3] == {6, 7}
assert max(len(neighbors[a] & neighbors[b]) for a, b in combinations(range(11), 2)) == 1
for mask in range(1 << 11):
    present = {v for v in range(11) if mask & (1 << v)}
    if 3 not in present:
        continue
    graph_value = any(a in present and b in present for a, b in edges)
    cofactor = 6 in present or 7 in present or any(a in present and b in present for a, b in core)
    assert cofactor == graph_value
print("Verified graph relabel, no four-cycle, and 1,024 true-cofactor rows.")
