"""Weighted rooted induced-even witness in a biconnected simple root block."""
from collections import deque


def search(adj, s, t, marked, target):
    """adj is a tuple of sets; marked and the returned support are vertex sets."""
    n = len(adj)
    root = frozenset((s, t))

    def root_cycle(forbidden):
        if s in forbidden or t in forbidden:
            return None
        queue = deque([s])
        prev = {s: None}
        while queue:
            u = queue.popleft()
            if u == t:
                path = set()
                while u is not None:
                    path.add(u)
                    u = prev[u]
                return path
            for v in adj[u]:
                if v not in forbidden and v not in prev and {u, v} != root:
                    prev[v] = u
                    queue.append(v)
        return None

    base = root_cycle(set())
    if base is None or len(base & marked) % 2 == target:
        return base
    for h in marked:
        cycle = root_cycle(adj[h] | {h})
        if cycle is not None:
            return cycle if len(cycle & marked) % 2 == target else cycle | {h}

    branch = {v for v in range(n) if len(adj[v]) != 2}
    if not branch:  # the entire root block is a cycle
        return None
    used = set()
    optional = []
    hard = []
    for u in branch:
        for v in adj[u]:
            edge = frozenset((u, v))
            if edge in used:
                continue
            route = [u, v]
            used.add(edge)
            while v not in branch:
                w, = adj[v] - {route[-2]}
                route.append(w)
                used.add(frozenset((v, w)))
                v = w
            if len(route) == 2:
                hard.append((u, v))
            else:
                optional.append(route)
    fixed = sorted({v for edge in hard for v in edge})
    extra = branch - set(fixed)
    for bits in range(1 << len(fixed)):
        chosen = extra | {v for i, v in enumerate(fixed) if bits >> i & 1}
        if (s in branch and s not in chosen) or (t in branch and t not in chosen):
            continue
        rhs = (target ^ (len(chosen & marked) % 2)) << n
        for u, v in hard:
            if u in chosen and v in chosen:
                rhs ^= (1 << u) ^ (1 << v)
        piv = {}
        for i, path in enumerate(optional):
            u, v = path[0], path[-1]
            is_root = any(frozenset(edge) == root for edge in zip(path, path[1:]))
            if is_root:
                rhs ^= 1 << (n + 1)
            if u not in chosen or v not in chosen:
                continue
            col = (1 << u) ^ (1 << v)
            col |= (len(set(path[1:-1]) & marked) % 2) << n
            if is_root:
                col |= 1 << (n + 1)
            x = 1 << i
            while col and col.bit_length() in piv:
                a, b = piv[col.bit_length()]
                col ^= a
                x ^= b
            if col:
                piv[col.bit_length()] = col, x
        x = 0
        while rhs and rhs.bit_length() in piv:
            a, b = piv[rhs.bit_length()]
            rhs ^= a
            x ^= b
        if not rhs:
            result = chosen.copy()
            for i, path in enumerate(optional):
                if x >> i & 1:
                    result.update(path)
            return result
    return None
