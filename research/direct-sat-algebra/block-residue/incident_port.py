"""Indexed port gadgets for compatible cycles of incident comparison pairs."""

from itertools import product

from branch_block import _blocks
from biclique_period import _insert


def _input(vertices, edges, pairs, *, incident=True):
    edges = tuple(tuple(edge) for edge in edges)
    pairs = tuple(tuple(pair) for pair in pairs)
    if not isinstance(vertices, int) or vertices < 0:
        raise ValueError("invalid vertex count")
    for x, y in edges:
        if not (0 <= x < vertices and 0 <= y < vertices):
            raise ValueError("invalid endpoint")
    used = set()
    for i, j in pairs:
        if not (0 <= i < len(edges) and 0 <= j < len(edges)):
            raise ValueError("invalid paired edge ID")
        if i == j or i in used or j in used:
            raise ValueError("pairs must be disjoint")
        if incident and not set(edges[i]).intersection(edges[j]):
            raise ValueError("paired edges must share a vertex")
        used.update((i, j))
    return edges, pairs


def _chords(vertices, edges):
    parent = list(range(vertices))

    def root(x):
        while x != parent[x]:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    chords = []
    for e, (x, y) in enumerate(edges):
        a, b = root(x), root(y)
        if a == b:
            chords.append(e)
        else:
            parent[a] = b
    return tuple(chords)


class PortGadget:
    """Simple gadget graph with zero-based gadget-edge coordinates.

    The chord coordinates index .chords, a tuple of original edge IDs.
    Deleted loops have zero gadget projection and supply independent units.
    """
    def __init__(self, vertices, edges, pairs):
        edges, pairs = _input(vertices, edges, pairs)
        self._build(range(vertices), edges, range(len(edges)), pairs,
                    _chords(vertices, edges))

    def _build(self, nodes, original, ids, pairs, chords):
        self.chords = chords
        self.original_ids = tuple(ids)
        self.loops = tuple(e for e in ids if original[e][0] == original[e][1])
        active = set(ids).difference(self.loops)
        grouped = {}
        for i, j in pairs:
            if i in active and j in active:
                x = min(set(original[i]).intersection(original[j]))
                grouped[x, i] = grouped[x, j] = min(i, j)

        edges = []
        self.vertices = 0

        def node():
            n = self.vertices
            self.vertices += 1
            return n

        def edge(x, y):
            edges.append((x, y))
            return len(edges) - 1

        self._centers = {}
        for x in nodes:
            a, b = node(), node()
            self._centers[x] = (a, b, edge(a, b))
        self._ports = {}
        self._paths = {}
        self.outer = {}
        for e in ids:
            if e not in active:
                continue
            keys = []
            for x in original[e]:
                key = (x, grouped.get((x, e), e))
                keys.append(key)
                if key not in self._ports:
                    p, m = node(), node()
                    a, b, _ = self._centers[x]
                    self._ports[key] = p, edge(p, m), edge(m, a), edge(m, b)
            a, b = node(), node()
            first = edge(self._ports[keys[0]][0], a)
            middle = edge(a, b)
            last = edge(b, self._ports[keys[1]][0])
            self.outer[e] = first
            self._paths[e] = (keys, first, middle, last)
        self.edges = tuple(edges)

    def project(self, mask):
        """Linearly read arbitrary gadget vectors, including hull-basis rows."""
        if not isinstance(mask, int) or mask < 0 or mask >> len(self.edges):
            raise ValueError("invalid gadget edge mask")
        return sum(1 << i for i, e in enumerate(self.chords)
                   if e in self.outer and mask >> self.outer[e] & 1)

    def lift(self, edge_ids):
        """Return a perfect matching for a loop-free compatible cycle union."""
        selected = set(edge_ids)
        if not selected.issubset(self._paths):
            raise ValueError("selected edge must be an original nonloop in this gadget")
        occupied = set()
        by_vertex = {}
        matching = 0
        for e, (keys, first, middle, last) in self._paths.items():
            if e in selected:
                matching |= (1 << first) | (1 << last)
                for key in keys:
                    if key in occupied:
                        raise ValueError("selected edges use the same local port")
                    occupied.add(key)
                    by_vertex.setdefault(key[0], []).append(key)
            else:
                matching |= 1 << middle
        for key, (_, internal, _, _) in self._ports.items():
            if key not in occupied:
                matching |= 1 << internal
        for x, (_, _, central) in self._centers.items():
            keys = by_vertex.get(x, ())
            if not keys:
                matching |= 1 << central
            elif len(keys) == 2:
                matching |= (1 << self._ports[keys[0]][2]) | (1 << self._ports[keys[1]][3])
            else:
                raise ValueError("selected degree must be zero or two")
        return matching


def block_gadgets(vertices, edges, pairs):
    """Build one gadget per edge block with shared global chord coordinates.

    A single simple cycle stays in one block; a pair split between blocks
    imposes no local restriction on a single-cycle generator.
    """
    edges, pairs = _input(vertices, edges, pairs)
    chords = _chords(vertices, edges)
    graph = [[] for _ in range(vertices)]
    for e, (x, y) in enumerate(edges):
        graph[x].append((y, e))
        if x != y:
            graph[y].append((x, e))
    result = []
    for block in _blocks(graph):
        ids = sorted(block)
        nodes = sorted({x for e in ids for x in edges[e]})
        gadget = PortGadget.__new__(PortGadget)
        gadget._build(nodes, edges, ids, pairs, chords)
        result.append(gadget)
    return tuple(result)


def forest_chords(vertices, edges):
    """Chord IDs for the input-order greedy spanning forest."""
    edges, _ = _input(vertices, edges, ())
    return _chords(vertices, edges)


def _compatible_cycles(ids, edges, pairs, coordinate):
    """Stream simple compatible cycles with original chord coordinates."""
    graph = {}
    mate = {a: b for i, j in pairs for a, b in ((i, j), (j, i))}
    for e in ids:
        x, y = edges[e]
        if x == y:
            yield coordinate[e]
        else:
            graph.setdefault(x, []).append((y, e))
            graph.setdefault(y, []).append((x, e))
    for start in graph:
        visited = {start}
        chosen = set()
        stack = [(start, None, 0, iter(graph[start]))]
        while stack:
            x, incoming, mask, neighbors = stack[-1]
            item = next(neighbors, None)
            if item is None:
                stack.pop()
                visited.remove(x)
                if incoming is not None:
                    chosen.remove(incoming)
                continue
            y, e = item
            if e == incoming or mate.get(e) in chosen or y < start:
                continue
            new_mask = mask ^ coordinate.get(e, 0)
            if y == start:
                yield new_mask
            elif y not in visited:
                chosen.add(e)
                visited.add(y)
                stack.append((y, e, new_mask, iter(graph[y])))


def _annihilator(table, width):
    rows = []
    for i in range(width):
        if i in table:
            continue
        x = 1 << i
        for p in sorted(table):
            if (x & table[p]).bit_count() % 2:
                x |= 1 << p
        rows.append(x)
    return tuple(rows)


def incident_directions(vertices, edges, pairs, *, method="auto"):
    """Compute universal primal directions in original forest-chord coordinates.

    DFS enumerates compatible simple cycles per original block. Hull branches
    only on nonincident pairs within each block and projects local perfect-
    matching span rows. Auto uses DFS for blocks of up to eight edges.
    """
    if method not in ("auto", "dfs", "hull"):
        raise ValueError("expected auto, dfs, or hull")
    edges, pairs = _input(vertices, edges, pairs, incident=False)
    chords = _chords(vertices, edges)
    coordinate = {e: 1 << i for i, e in enumerate(chords)}
    graph = [[] for _ in range(vertices)]
    for e, (x, y) in enumerate(edges):
        graph[x].append((y, e))
        if x != y:
            graph[y].append((x, e))
    dual = {}
    for ids in _blocks(graph):
        members = set(ids)
        internal = [(a, b) for a, b in pairs if a in members and b in members]
        if len(ids) == 1:
            e = ids[0]
            if edges[e][0] == edges[e][1]:
                _insert(dual, coordinate[e])
            continue
        if method == "dfs" or (method == "auto" and len(ids) <= 8):
            for mask in _compatible_cycles(ids, edges, internal, coordinate):
                _insert(dual, mask)
            continue

        from matching_hull import matching_hull

        incident = []
        branch = []
        for a, b in internal:
            dest = incident if set(edges[a]).intersection(edges[b]) else branch
            dest.append((a, b))
        for sides in product((0, 1), repeat=len(branch)):
            removed = {pair[side] for pair, side in zip(branch, sides)}
            keep = [e for e in ids if e not in removed]
            nodes = sorted({x for e in keep for x in edges[e]})
            gadget = PortGadget.__new__(PortGadget)
            gadget._build(nodes, edges, keep, incident, chords)
            m = len(gadget.edges)
            read = (1 << m) - 1
            for row in matching_hull(range(gadget.vertices), gadget.edges):
                _insert(dual, gadget.project(row & read))
    return _annihilator(dual, len(chords))
