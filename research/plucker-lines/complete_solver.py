"""Witness search for the two-sided shared-only problem with complete colored block."""
from collections import deque
from itertools import combinations


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def search(rows, left, right):
    """Return a support bitmask, or None. Colors 0,1 are ordinary, 2 is shared."""
    h = len(left)
    labels = list(left) + list(right)
    n = len(labels)
    adj = [r << h for r in rows] + [sum(1 << i for i, r in enumerate(rows) if r >> j & 1)
                                      for j in range(len(right))]
    L = (1 << h)-1
    R = ((1 << n)-1) ^ L
    S = sum(1 << i for i, r in enumerate(labels) if r == 2)
    P, Q = L & ~S, R & ~S
    if any(adj[i]&Q != Q for i in bits(P)):
        raise ValueError("colored block must be complete")
    def path(i, j, allowed):
        queue = deque([i])
        prev = {i:None}
        while queue:
            u = queue.popleft()
            for v in bits(adj[u] & (allowed | ((1 << j) if u != i else 0))):
                if v in prev:
                    continue
                prev[v] = u
                if v == j:
                    x = 0
                    while v is not None:
                        x |= 1 << v
                        v = prev[v]
                    return x
                queue.append(v)
        return 0
    cycles = []
    for i in bits(P):
        for j in bits(Q):
            cyc = path(i,j,S)
            if not cyc:
                continue
            if labels[i] == labels[j]:
                return cyc
            cycles.append((i, j, cyc))
            for k in bits(S & ~(adj[i]|adj[j])):
                witness = path(i,j,S & ~(adj[k] | (1 << k)))
                if witness:
                    return witness | (1 << k)
    if not cycles:
        return None
    # Every bi-contact component forces its participants to see all opposite
    # shared isolates. If another nonisolated component exists, those contacts
    # see it as well, hence it too is bi-contact.
    paired = sum(1 << i for i in bits(S) if adj[i]&S)
    isolates = S ^ paired
    participating = sum(1 << i for i in bits(P|Q) if adj[i]&paired)
    cyc = cycles[0][2]
    for side in (P, Q):
        for a,b in combinations(bits(side & ~participating), 2):
            if labels[a] == labels[b]:
                continue
            aonly = adj[a] & ~adj[b] & isolates
            bonly = adj[b] & ~adj[a] & isolates
            if aonly and bonly:
                return cyc | (1 << a) | (1 << b) | (aonly & -aonly) | (bonly & -bonly)
    return None
