"""Polynomial witness search for a noncomplete colored block; labels 0,1,2 (shared)."""
from itertools import combinations
from collections import deque


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def parity(mask):
    return mask.bit_count() % 2


def search(rows, left, right):
    h = len(left)
    labels = list(left) + list(right)
    n = len(labels)
    adj = [r << h for r in rows] + [sum(1 << i for i, r in enumerate(rows) if r >> j & 1)
                                      for j in range(len(right))]
    L = (1 << h)-1
    R = ((1 << n)-1) ^ L
    S = sum(1 << i for i, r in enumerate(labels) if r == 2)
    P, Q = L & ~S, R & ~S
    third = sum(1 << i for i, r in enumerate(labels) if r != 0)
    def valid(x):
        return parity(x&P) and parity(x&Q) and not parity(x&third) and all(not parity(adj[i]&x) for i in bits(x))

    DL = sum(1 << i for i in bits(P) if Q & ~adj[i])
    DR = sum(1 << j for j in bits(Q) if P & ~adj[j])
    if not DL:
        raise ValueError("colored block must have a nonedge")
    for k in (2, 3, 5, 6):
        for part in combinations(range(n), k):
            x = sum(1 << i for i in part)
            if valid(x):
                return x
    if not any(adj[i] & S for i in bits(L&S)):
        return None

    for i in bits(P):
        for j in bits(Q):
            if labels[i] != labels[j]:
                continue
            prev = {i: None}
            queue = deque([i])
            while queue and j not in prev:
                v = queue.popleft()
                allowed = S | ((1 << j) if v != i else 0)
                for w in bits(adj[v] & allowed):
                    if w not in prev:
                        prev[w] = v
                        queue.append(w)
            if j in prev:
                x, v = 0, j
                while v is not None:
                    x |= 1 << v
                    v = prev[v]
                assert valid(x)
                return x

    # Transitive closure of the shared tournament; predecessor counts strictly
    # separate comparable SCCs of its condensation.
    reach = {i: (1 << i) | ((adj[i] & R & S) if i < h else (~adj[i] & L & S)) for i in bits(S)}
    for k in bits(S):
        for i in bits(S):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    comps = {}
    for i in bits(S):
        comp = sum(1 << j for j in bits(reach[i]) if reach[j] >> i & 1)
        comps[comp] = sum(bool(reach[j] & (1 << i)) for j in bits(S))
    ordered = sorted(comps, key=lambda comp: (comps[comp], comp))
    base = []
    for c in ordered:
        if base and ((not ((base[-1]|c)&L)) or (not ((base[-1]|c)&R))):
            base[-1] |= c
        else:
            base.append(c)
    boxes = base.copy()
    slots = [[] for _ in range(len(boxes)+1)]
    for i in bits((P|Q) & ~(DL|DR)):
        shore = R if i < h else L
        H = adj[i] & S
        partial = [k for k, c in enumerate(base) if c & H and c & shore & ~H]
        if partial:
            assert len(partial) == 1
            boxes[partial[0]] |= 1 << i
        else:
            full = [k for k, c in enumerate(base) if c & H]
            slot = max(full, default=-1)+1 if i < h else min(full, default=len(boxes))
            slots[slot].append(1 << i)
    order = [DL|DR]
    for k, box in enumerate(boxes):
        order.extend(slots[k])
        order.append(box)
    order.extend(slots[-1])
    # Types DL, DR, SL, SR, UL0, UL1, UR0, UR1.
    types = [(0 if DL >> i & 1 else 1 if DR >> i & 1 else 2 if i < h and S >> i & 1
              else 3 if S >> i & 1 else 4+labels[i] if i < h else 6+labels[i]) for i in range(n)]
    def profile(x):
        v = 0
        for i in bits(x):
            v ^= 1 << types[i]
        return v
    present = sum(1 << t for t in set(types))
    # Build actual external masks and certify that one coefficient per type
    # per orientation represents the graph.
    tables = []
    prior = 0
    for box in order:
        later = ((1 << n)-1) & ~(prior|box)
        req = {}
        for i in bits(box):
            pair = []
            for ext in (prior, later):
                mask = 0
                for t in set(types):
                    sl = sum(1 << j for j in bits(ext) if types[j] == t)
                    meet = adj[i] & sl
                    assert not meet or meet == sl
                    if meet:
                        mask |= 1 << t
                pair.append(mask)
            req[i] = tuple(pair)
        entries = []
        for k in range(min(4,box.bit_count())+1):
            for part in combinations(bits(box), k):
                x = sum(1 << i for i in part)
                conditions = frozenset((req[i][0], req[i][1], parity(adj[i]&x)) for i in part)
                entries.append((profile(x),conditions,x))
        tables.append(entries)
        prior |= box
    for total in range(256):
        if total & ~present:
            continue
        rep = sum(1 << next(i for i in range(n) if types[i] == t) for t in bits(total))
        if not parity(rep&P) or not parity(rep&Q) or parity(rep&third):
            continue
        states = {0:0}
        for entries in tables:
            nxt = {}
            for prefix, witness in states.items():
                for local, conds, selected in entries:
                    after = prefix ^ local
                    if after in nxt:
                        continue
                    suffix = after ^ total
                    if all(parity(m&prefix)^parity(l&suffix) == need for m,l,need in conds):
                        nxt[after] = witness|selected
            states = nxt
        if total in states:
            assert valid(states[total])
            return states[total]
    return None
