"""Find x with x_i (A x)_i = 0 and an accepted affine marker, for symmetric A."""
from collections import deque


def marker_witness(rows, markers):
    n = len(rows)
    if any(m < 0 or m >= 1 << n for m in rows):
        raise ValueError("row outside matrix")
    if any(bool(rows[i] & (1 << j)) != bool(rows[j] & (1 << i))
           for i in range(n) for j in range(i)):
        raise ValueError("matrix must be symmetric")
    for mask, bias in markers:
        if mask < 0 or mask >= 1 << n or bias not in (0, 1):
            raise ValueError("invalid marker")
        if bias:
            return 0
        marked = [i for i in range(n) if rows[i] & (1 << i)]
        marked_set = set(marked)
        for i in range(n):
            if i not in marked_set and mask & (1 << i):
                return 1 << i
        # A multi-source BFS from all marked vertices labeled 0 seeks a marked
        # vertex labeled 1. On a shortest such path all internal vertices are
        # unmarked. A chord would give a shorter path.
        roots = [i for i in marked if not mask & (1 << i)]
        predecessor = {i: None for i in roots}
        queue = deque(roots)
        while queue:
            u = queue.popleft()
            if u in marked_set and mask & (1 << u):
                path = 0
                while u is not None:
                    path |= 1 << u
                    u = predecessor[u]
                return path
            for v in range(n):
                if rows[u] & (1 << v) and v not in predecessor:
                    predecessor[v] = u
                    queue.append(v)
    return None


def verify():
    checks = 0
    for n in range(1, 5):
        upper = [(i, j) for i in range(n) for j in range(i, n)]
        for encoding in range(1 << len(upper)):
            rows = [0] * n
            for k, (i, j) in enumerate(upper):
                if encoding & (1 << k):
                    rows[i] |= 1 << j
                    rows[j] |= 1 << i
            feasible = [x for x in range(1 << n)
                        if all(not x & (1 << i) or (x & row).bit_count() % 2 == 0
                               for i, row in enumerate(rows))]
            for mask in range(1 << n):
                candidates = [x for x in feasible if (x & mask).bit_count() % 2]
                ans = marker_witness(rows, [(mask, 0)])
                assert (ans is None and not candidates) or ans in candidates
                checks += 1
    print(f"Checked all {checks} symmetric matrix/marker pairs through dimension four.")


if __name__ == "__main__":
    verify()
