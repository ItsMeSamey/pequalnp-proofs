"""Test five distinct local stabilizers whose every three span CCZ in dimension three."""
import itertools
import runpy
from collections import Counter
from pathlib import Path
import numpy as np
source = runpy.run_path(str(Path(__file__).with_name("product-plane-control.py")))
stabs, orbit_reps, quotient, groups, unit, p = (source[k] for k in ("stabs","orbit_reps","quotient","groups","unit","p"))
phases = stabs()
A = np.array([[0 if v < 0 else unit[v] for v in row] for row in phases], dtype=np.int64)
g = np.array([1]*7+[p-1], dtype=np.int64)
Q = quotient(A,g)
planes = set()
for i, _ in orbit_reps(phases):
    M = quotient(Q,Q[i])
    base = np.where(~M.any(axis=1))[0].tolist()
    for J in groups(M):
        if J[0] not in base and len(base)+len(J)>=5:
            planes.add(tuple(sorted(base+J)))
counts = Counter()
for ids in planes:
    F = A[list(ids)]
    m = len(ids)
    bad = set()
    for i in range(m):
        N = quotient(np.vstack((F,g)),F[i])
        for J in groups(N):
            if i not in J and m not in J:
                bad.update(itertools.combinations(sorted([i]+J),3))
    for subset in itertools.combinations(range(m),5):
        if not any(triple in bad for triple in itertools.combinations(subset,3)):
            counts[m] += 1
print("planes", dict(Counter(map(len,planes))), "robust five-sets", dict(counts))
