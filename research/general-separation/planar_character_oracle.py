"""Exact character sums on named-edge planar bipartite perfect matchings."""
from ring_image_planar_demands import _sign


class DeterminantBudget(Exception):
    def __init__(self, required, available):
        self.required = required
        self.available = available
        super().__init__("determinant budget exceeded")


def _signed_det(matrix):
    """Signed fraction-free elimination; a row swap negates the determinant."""
    n = len(matrix)
    if not n:
        return 1
    previous = sign = 1
    for j in range(n-1):
        pivot = next((u for u in range(j, n) if matrix[u][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[pivot], matrix[j] = matrix[j], matrix[pivot]
            sign = -sign
        current = matrix[j][j]
        for i in range(j+1, n):
            for h in range(j+1, n):
                matrix[i][h] = (current*matrix[i][h] - matrix[i][j]*matrix[j][h]) // previous
        previous = current
    return sign * matrix[-1][-1]


class CharacterOracle:
    """One fixed simple root/signing and a cumulative sequential-query budget."""
    def __init__(self, root, *, max_determinants=None):
        import networkx as nx
        if max_determinants is not None and (type(max_determinants) is not int or
                                              max_determinants < 0):
            raise ValueError("invalid determinant budget")
        if root.is_multigraph() or root.is_directed() or nx.number_of_selfloops(root):
            raise ValueError("root must be simple and undirected")
        if not nx.is_bipartite(root):
            raise ValueError("root must be bipartite")
        self.max_determinants = max_determinants
        self.calls = 0
        self._edges = {}
        self._incident = {u: set() for u in root}
        for u, v, data in root.edges(data=True):
            x = data.get("variable")
            if type(x) is not int or x <= 0 or x in self._edges:
                raise ValueError("expected distinct positive integer edge IDs")
            self._edges[x] = (u, v)
            self._incident[u].add(x)
            self._incident[v].add(x)
        color = nx.bipartite.color(root)
        left = {u: j for j, u in enumerate(u for u in root if color[u])}
        right = {u: j for j, u in enumerate(u for u in root if not color[u])}
        self._size = len(left)
        self._base = 1 if not len(root) else None
        negative = set()
        for nodes in nx.connected_components(root):
            if 2 * sum(color[u] for u in nodes) != len(nodes):
                self._base = 0
            if len(nodes) > 1:
                signing = _sign(nx, root.subgraph(nodes))
                if signing is None:
                    raise ValueError("root must be planar")
                negative.update(signing)
        self._entries = {}
        for x, (u, v) in self._edges.items():
            if u not in left:
                u, v = v, u
            self._entries[x] = left[u], right[v], -1 if x in negative else 1

    def _ids(self, items):
        out = set()
        for x in items:
            if type(x) is not int or x not in self._edges:
                raise ValueError("unknown edge ID")
            out.add(x)
        return out

    def _det(self, forbidden, negative):
        if self.max_determinants is not None and self.calls >= self.max_determinants:
            raise DeterminantBudget(self.calls+1, self.max_determinants)
        matrix = [[0] * self._size for _ in range(self._size)]
        for x, (u, v, sign) in self._entries.items():
            if x not in forbidden:
                matrix[u][v] = -sign if x in negative else sign
        self.calls += 1
        return _signed_det(matrix)

    def count(self, *, negative=(), deleted=(), pinned=()):
        """Signed sum over perfect matchings containing pinned and avoiding deleted."""
        negative = self._ids(negative)
        forbidden = self._ids(deleted)
        pinned = self._ids(pinned)
        for x in pinned:
            for u in self._edges[x]:
                forbidden.update(self._incident[u] - {x})
        if pinned & forbidden or self._base == 0:
            return 0
        if self._base is None:
            self._base = self._det(set(), set())
            if not self._base:
                return 0
        negative.difference_update(forbidden)
        if not forbidden and not negative:
            return abs(self._base)
        value = self._det(forbidden, negative)
        return value if self._base > 0 else -value
