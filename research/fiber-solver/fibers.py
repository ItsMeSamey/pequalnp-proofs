"""Decision and witness extraction for finite binary CSPs on explicit domains."""
from collections import defaultdict, deque


def solve(domains, edges):
    """Return ('sat', witness), ('unsat', None), or ('unsupported', None).

    Each edge is (u,v,allowed_pairs). Arc consistency precedes recognition.
    Domain values and vertex names must be hashable.
    """
    d = {u: set(values) for u, values in domains.items()}
    tables = []
    for u, v, pairs in edges:
        pairs = {(a, b) for a, b in pairs if a in d[u] and b in d[v]}
        if u == v:
            d[u] &= {a for a, b in pairs if a == b}
        else:
            tables.append((u, v, pairs))
    changed = True
    while changed:
        changed = False
        for u, v, pairs in tables:
            live = [(a, b) for a, b in pairs if a in d[u] and b in d[v]]
            for vertex, support in ((u, {a for a,b in live}), (v, {b for a,b in live})):
                if support != d[vertex]:
                    d[vertex] = support
                    changed = True
    if any(not values for values in d.values()):
        return 'unsat', None

    partitions = {}
    graph = defaultdict(list)
    for u, v, pairs in tables:
        rows = defaultdict(set)
        for a, b in pairs:
            if a in d[u] and b in d[v]:
                rows[a].add(b)
        groups = defaultdict(set)
        for a, neighbors in rows.items():
            groups[frozenset(neighbors)].add(a)
        if sum(map(len, groups)) != len(d[v]):
            return 'unsupported', None
        forward = {frozenset(left): right for right, left in groups.items()}
        if len(forward) == 1:
            continue
        reverse = {r: l for l, r in forward.items()}
        for vertex, mapping in ((u, forward), (v, reverse)):
            partition = frozenset(mapping)
            if partitions.setdefault(vertex, partition) != partition:
                return 'unsupported', None
        graph[u].append((v, forward))
        graph[v].append((u, reverse))

    witness = {}
    for root in d:
        if root in witness:
            continue
        if root not in partitions:
            witness[root] = next(iter(d[root]))
            continue
        for block in partitions[root]:
            assignment = {root: block}
            queue = deque([root])
            consistent = True
            while queue and consistent:
                u = queue.popleft()
                for v, mapping in graph[u]:
                    required = mapping[assignment[u]]
                    if v not in assignment:
                        assignment[v] = required
                        queue.append(v)
                    elif assignment[v] != required:
                        consistent = False
                        break
            if consistent:
                witness.update({u: next(iter(b)) for u, b in assignment.items()})
                break
        else:
            return 'unsat', None
    return 'sat', witness
