from itertools import combinations_with_replacement


def par(x):
    return x.bit_count() % 2


def symmetric_maps(t):
    slots = list(combinations_with_replacement(range(t),2))
    for code in range(1<<len(slots)):
        rows = [0]*t
        for j,(a,b) in enumerate(slots):
            if code>>j&1:
                rows[a] |= 1<<b
                rows[b] |= 1<<a
        yield [sum(par(r&v)<<i for i,r in enumerate(rows)) for v in range(1<<t)]


def solve(A, labels, t):
    """Return a mask witness per reachable label, or raise ValueError outside the class."""
    q=1<<t
    maps=list(symmetric_maps(t))
    def node(vertices):
        if len(vertices)==1:
            i=next(iter(vertices))
            return [{0:0, **({labels[i]:1<<i} if ((A[i]>>i)&1)==par(labels[i]&s) else {})}
                    for s in range(q)]
        for K in maps:
            start=next(iter(vertices))
            seen={start}
            stack=[start]
            while stack:
                i=stack.pop()
                for j in vertices-seen:
                    if ((A[i]>>j)&1) != par(labels[i]&K[labels[j]]):
                        seen.add(j)
                        stack.append(j)
            if len(seen)<len(vertices):
                left=node(seen)
                right=node(vertices-seen)
                table=[{} for _ in range(q)]
                for s in range(q):
                    for p in range(q):
                        for r in range(q):
                            lhs=left[s^K[r]]
                            rhs=right[s^K[p]]
                            if p in lhs and r in rhs:
                                table[s][p^r]=lhs[p]|rhs[r]
                return table
        raise ValueError("no decomposition")
    if not A:return {0:0}
    return node(set(range(len(A))))[0]
