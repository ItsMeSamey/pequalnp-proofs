"""Project degree-two comparison paths from clauses of arbitrary arity."""

from collections.abc import Mapping


class PathKernel:
    """Projected clauses use original vertex IDs. Each occurrence stays distinct."""

    def __init__(self, vertices, clauses):
        if not isinstance(vertices, int) or vertices < 0:
            raise ValueError("expected a nonnegative vertex count")
        self.vertices = vertices
        edges = []
        owners = []
        graph = [[] for _ in range(vertices)]
        clause_count = 0
        for clause_count, clause in enumerate(clauses, 1):
            for x, y, d in clause:
                if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
                    raise ValueError("invalid signed comparison")
                e = len(edges)
                edges.append((x, y, d))
                owners.append(clause_count - 1)
                graph[x].append(e)
                graph[y].append(e)

        used = bytearray(len(edges))
        paths = []
        requests = []

        def walk(x, e):
            start = x
            path = []
            target = 0
            while True:
                used[e] = 1
                u, v, d = edges[e]
                y = v if x == u else u
                path.append((e, y, d))
                target ^= d
                if len(graph[y]) != 2:
                    break
                first, second = graph[y]
                nxt = second if first == e else first
                if used[nxt]:
                    break
                x, e = y, nxt
            paths.append(path)
            requests.append((start, y, target))

        for x, neighborhood in enumerate(graph):
            if len(neighborhood) != 2:
                for e in neighborhood:
                    if not used[e]:
                        walk(x, e)
        for e, (x, _, _) in enumerate(edges):
            if not used[e]:
                walk(x, e)

        count = len(paths)
        incidence = [[] for _ in range(count + clause_count)]
        for p, path in enumerate(paths):
            for e, _, _ in path:
                c = count + owners[e]
                incidence[p].append((c, e))
                incidence[c].append((p, e))

        self._components = []
        seen = bytearray(len(incidence))
        tree = bytearray(len(edges))
        projected = []
        for root in range(len(incidence)):
            if seen[root]:
                continue
            seen[root] = 1
            pending = [root]
            members = []
            extra = None
            while pending:
                x = pending.pop()
                members.append(x)
                for y, e in incidence[x]:
                    if not seen[y]:
                        seen[y] = 1
                        tree[e] = 1
                        pending.append(y)
                    elif not tree[e] and extra is None:
                        extra = (x, e)
            ps = [p for p in members if p < count]
            if extra is None:
                projected.append(tuple(requests[p] for p in ps))
            self._components.append((ps, extra))
        self._tree = tree
        self._incidence = incidence
        self._paths = paths
        self._requests = requests
        retained = bytearray(vertices)
        for x, y, _ in requests:
            retained[x] = retained[y] = 1
        self.endpoints = tuple(v for v in range(vertices) if retained[v])
        self.clauses = tuple(projected)

    def lift(self, values):
        """Lift endpoint bits or return None for an unsatisfied projected clause.

        Accept a sequence indexed by original vertex ID or a mapping. Omitted
        mapping keys default to zero, including endpoints absent from clauses.
        The linear RAM bound uses an indexed sequence; for a mapping, add
        the costs of its individual lookups.
        """
        result = [0] * self.vertices
        for v in self.endpoints:
            bit = values.get(v, 0) if isinstance(values, Mapping) else values[v]
            if bit not in (0, 1):
                raise ValueError("invalid endpoint bit")
            result[v] = bit
        good = [(result[x] ^ result[y]) == d for x, y, d in self._requests]
        failures = bytearray(len(self._tree))
        for ps, extra in self._components:
            if extra is None:
                root = next((p for p in ps if good[p]), None)
                if root is None:
                    return None
            else:
                root, e = extra
                if root < len(good) and not good[root]:
                    failures[e] = 1
            # Each bad path selects its outgoing incidence. Each clause keeps
            # its own outgoing incidence true (opposite use is impossible).
            pending = [(root, None)]
            while pending:
                x, parent_edge = pending.pop()
                for y, e in self._incidence[x]:
                    if e == parent_edge or not self._tree[e]:
                        continue
                    if y < len(good) and not good[y]:
                        failures[e] = 1
                    pending.append((y, e))
        for p, path in enumerate(self._paths):
            x, end, _ = self._requests[p]
            bit = result[x]
            for e, y, d in path:
                bit ^= d ^ failures[e]
                if y == end:
                    if bit != result[y]:
                        raise AssertionError("path parity failed to lift")
                else:
                    result[y] = bit
        return result


def path_kernel(vertices, clauses):
    """Build a one-pass kernel and retain the data needed for witness lifting."""
    return PathKernel(vertices, clauses)
