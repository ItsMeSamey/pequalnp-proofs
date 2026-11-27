"""Maximal one-sided peeling of signed-balanced blocks and simple cycles."""

from dataclasses import dataclass

from balanced_block import _potentials


def _blocks(vertices, edges):
    """Tarjan edge blocks and potentials on the DFS forest. Loops stand alone."""
    graph = [[] for _ in range(vertices)]
    blocks = []
    for e, (x, y, d) in enumerate(edges):
        if x == y:
            blocks.append([e])
        else:
            graph[x].append((y, e))
            graph[y].append((x, e))

    discovery = [-1] * vertices
    low = [0] * vertices
    values = [0] * vertices
    incoming = [-1] * vertices
    cursor = [0] * vertices
    edge_stack = []
    clock = 0
    for root in range(vertices):
        if discovery[root] != -1:
            continue
        discovery[root] = low[root] = clock
        clock += 1
        stack = [root]
        while stack:
            x = stack[-1]
            if cursor[x] == len(graph[x]):
                stack.pop()
                if stack:
                    p = stack[-1]
                    low[p] = min(low[p], low[x])
                    if low[x] >= discovery[p]:
                        block = []
                        while True:
                            e = edge_stack.pop()
                            block.append(e)
                            if e == incoming[x]:
                                break
                        blocks.append(block)
                continue
            y, e = graph[x][cursor[x]]
            cursor[x] += 1
            if discovery[y] == -1:
                edge_stack.append(e)
                incoming[y] = e
                discovery[y] = low[y] = clock
                clock += 1
                values[y] = values[x] ^ edges[e][2]
                stack.append(y)
            elif e != incoming[x] and discovery[y] < discovery[x]:
                edge_stack.append(e)
                low[x] = min(low[x], discovery[y])
    return blocks, values


def _cycle_choices(edges, block_of, kinds):
    """Map each peelable unbalanced cycle to the comparison to make false."""
    neighbors = [[] for _ in kinds]
    private = {}
    for e in range(0, len(edges), 2):
        a, b = block_of[e], block_of[e + 1]
        if kinds[a] == kinds[b] == "cycle":
            neighbors[a].append((b, e))
            neighbors[b].append((a, e + 1))
        elif kinds[a] == "cycle" and kinds[b] == "clean":
            private[a] = e
        elif kinds[b] == "cycle" and kinds[a] == "clean":
            private[b] = e + 1

    seen = set()
    choices = {}
    for start, kind in enumerate(kinds):
        if kind != "cycle" or start in seen:
            continue
        seen.add(start)
        stack = [start]
        tree_shells = set()
        spare = None
        while stack:
            a = stack.pop()
            if a in private:
                spare = a, private[a]
            for b, edge in neighbors[a]:
                shell = edge // 2
                if b not in seen:
                    seen.add(b)
                    tree_shells.add(shell)
                    stack.append(b)
                elif shell not in tree_shells:
                    spare = a, edge
        if spare is None:
            continue
        # Root the spanning tree at an owner of a private or non-tree
        # resource. Other vertices can each use their parent shell.
        root, root_edge = spare
        choices[root] = root_edge
        stack = [root]
        while stack:
            a = stack.pop()
            for b, edge in neighbors[a]:
                if edge // 2 in tree_shells and b not in choices:
                    choices[b] = edge ^ 1
                    stack.append(b)
    return choices


@dataclass
class Autarky:
    """Residual comparisons refer to the original comparison vertex IDs."""
    vertices: int
    residual_shells: tuple
    residual_comparisons: tuple
    _edges: tuple
    _peeled: tuple
    _zeros: frozenset
    _raw_coordinates: tuple | None = None

    def lift(self, vertex_values=None):
        """Extend a residual vertex witness; signed-copy mode returns raw bits."""
        if vertex_values is None:
            if self.residual_shells:
                raise ValueError("a residual vertex witness is required")
            vertex_values = [0] * self.vertices
        if len(vertex_values) != self.vertices or any(v not in (0, 1) for v in vertex_values):
            raise ValueError("invalid residual vertex values")
        for shell in self.residual_shells:
            pair = self._edges[2*shell:2*shell+2]
            if not any((vertex_values[x] ^ vertex_values[y]) == d for x, y, d in pair):
                raise ValueError("residual witness violates a shell")

        # Preserve retained differences. Absolute labels across interior
        # articulations may need independent flips on descendant blocks.
        graph = [[] for _ in range(self.vertices)]
        for e, (x, y, d) in enumerate(self._edges):
            if self._peeled[e]:
                difference = d ^ (e in self._zeros)
            else:
                difference = vertex_values[x] ^ vertex_values[y]
            graph[x].append((y, difference))
            graph[y].append((x, difference))
        result = _potentials(graph)
        if result is None:
            raise AssertionError("blockwise differences failed to glue")
        values = result[1]
        if self._raw_coordinates is None:
            return values
        return [values[x] ^ s for x, s in self._raw_coordinates]


def comparison_autarky(vertices, comparisons):
    """Peel paired (u,v,d) comparisons; a true comparison meets XOR target d."""
    edges = tuple(tuple(edge) for edge in comparisons)
    if not isinstance(vertices, int) or vertices < 0 or len(edges) % 2:
        raise ValueError("expected nonnegative vertex count and paired comparisons")
    for x, y, d in edges:
        if not (0 <= x < vertices and 0 <= y < vertices and d in (0, 1)):
            raise ValueError("invalid signed comparison")
    blocks, tree_values = _blocks(vertices, edges)
    block_of = [-1] * len(edges)
    kinds = []
    for i, block in enumerate(blocks):
        pts = set()
        balanced = True
        for e in block:
            x, y, d = edges[e]
            pts.update((x, y))
            block_of[e] = i
            if (tree_values[x] ^ tree_values[y]) != d:
                balanced = False
        if balanced:
            kinds.append("clean")
        elif len(pts) == len(block):
            kinds.append("cycle")
        else:
            kinds.append("hard")

    choices = _cycle_choices(edges, block_of, kinds)
    peeled = tuple(kinds[i] == "clean" or i in choices for i in block_of)
    residual = tuple(i for i in range(len(edges) // 2)
                     if not peeled[2*i] and not peeled[2*i+1])
    residual_edges = tuple(edges[2*i+j] for i in residual for j in (0, 1))
    return Autarky(vertices, residual, residual_edges, edges, peeled,
                   frozenset(choices.values()))


def raw_autarky(shells, pins):
    """Peel four-bit matching shells; return None on inconsistent signed pins.

    Each shell stores the left color's two bits, then the right color's bits.
    Residual vertex IDs are compact signed-copy class indices. Pass an
    assignment in that namespace to lift() to recover every original raw bit.
    """
    if not isinstance(shells, int) or shells < 0:
        raise ValueError("expected nonnegative shell count")
    n = 4 * shells
    links = [[] for _ in range(n)]
    for a, b, s in pins:
        if not (0 <= a < n and 0 <= b < n and s in (0, 1)):
            raise ValueError("invalid copy pin")
        links[a].append((b, s))
        links[b].append((a, s))
    solution = _potentials(links)
    if solution is None:
        return None
    roots, offsets = solution
    ids = {root: i for i, root in enumerate(dict.fromkeys(roots))}
    raw = tuple((ids[r], s) for r, s in zip(roots, offsets))
    comparisons = []
    for shell in range(shells):
        for pos in (0, 1):
            a = 4*shell + pos
            x, s = raw[a]
            y, t = raw[a+2]
            comparisons.append((x, y, 1 ^ s ^ t))
    result = comparison_autarky(len(ids), comparisons)
    result._raw_coordinates = raw
    return result
