"""Four-color matching shells with signed equality pins on raw coordinates."""

from collections import deque


class NonCactusError(ValueError):
    """The comparison multigraph has overlapping simple cycles."""


def _repair(cycles):
    """Match each violated cycle to a shell in which its comparison can be zero."""
    owner = {}
    chosen = {}
    for start in range(len(cycles)):
        queue = deque([start])
        reached_by = {}
        seen = {start}
        free = None
        while queue and free is None:
            cycle = queue.popleft()
            for edge in cycles[cycle]:
                shell = edge // 2
                if shell in reached_by:
                    continue
                reached_by[shell] = cycle, edge
                if shell not in owner:
                    free = shell
                    break
                neighbor = owner[shell]
                if neighbor not in seen:
                    queue.append(neighbor)
                    seen.add(neighbor)
        if free is None:
            return None
        while True:
            cycle, edge = reached_by[free]
            old_edge = chosen.get(cycle)
            owner[free] = cycle
            chosen[cycle] = edge
            if old_edge is None:
                break
            free = old_edge // 2
    return set(chosen.values())


def cactus_witness(shells, pins):
    """Return raw bits or None for UNSAT; raise NonCactusError outside the class.

    Shell i compares colors (4i,4i+1) and (4i+2,4i+3). Each pin (a,b,s)
    imposes raw[a] XOR raw[b] = s. Inconsistent pins imply UNSAT outright.
    """
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected a nonnegative number of shells")
    n = 4 * shells
    links = [[] for _ in range(n)]
    for a, b, sign in pins:
        if not (0 <= a < n and 0 <= b < n and sign in (0, 1)):
            raise ValueError("invalid signed pin")
        links[a].append((b, sign))
        links[b].append((a, sign))

    component = [-1] * n
    offset = [0] * n
    classes = 0
    for root in range(n):
        if component[root] >= 0:
            continue
        component[root] = classes
        classes += 1
        stack = [root]
        while stack:
            a = stack.pop()
            for b, sign in links[a]:
                required = offset[a] ^ sign
                if component[b] == -1:
                    component[b] = component[a]
                    offset[b] = required
                    stack.append(b)
                elif offset[b] != required:
                    return None

    graph = [[] for _ in range(classes)]
    endpoints = []
    desired = []
    for shell in range(shells):
        for position in range(2):
            a = 4 * shell + position
            b = a + 2
            x, y = component[a], component[b]
            edge = len(endpoints)
            endpoints.append((x, y))
            # Required class difference when the raw comparison differs.
            desired.append(1 ^ offset[a] ^ offset[b])
            graph[x].append((y, edge))
            graph[y].append((x, edge))

    parent = [-1] * classes
    parent_edge = [-1] * classes
    depth = [0] * classes
    order = []
    tree = set()
    for root in range(classes):
        if parent[root] != -1:
            continue
        parent[root] = root
        stack = [root]
        while stack:
            x = stack.pop()
            order.append(x)
            for y, edge in graph[x]:
                if parent[y] == -1:
                    parent[y] = x
                    parent_edge[y] = edge
                    depth[y] = depth[x] + 1
                    tree.add(edge)
                    stack.append(y)

    # Edge-disjoint fundamental cycles characterize a cactus (including
    # loops and two-edge cycles). Their XOR equations suffice for a lift.
    used = set()
    violations = []
    for edge, (x, y) in enumerate(endpoints):
        if edge in tree:
            continue
        cycle = [edge]
        parity = desired[edge]
        while x != y:
            if depth[x] < depth[y]:
                x, y = y, x
            step = parent_edge[x]
            if step in used:
                raise NonCactusError("comparison edge belongs to overlapping cycles")
            used.add(step)
            cycle.append(step)
            parity ^= desired[step]
            x = parent[x]
        if parity:
            violations.append(cycle)
    zeros = _repair(violations)
    if zeros is None:
        return None
    values = [0] * classes
    for y in order:
        if y != parent[y]:
            edge = parent_edge[y]
            values[y] = values[parent[y]] ^ desired[edge] ^ (edge in zeros)
    return [values[component[i]] ^ offset[i] for i in range(n)]
