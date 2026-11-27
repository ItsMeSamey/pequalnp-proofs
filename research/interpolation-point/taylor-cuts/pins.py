"""Deterministic signed pins and sparse-syndrome search for circle words."""
from itertools import product
import networkx as nx
from circle_parity_solver import _gadget, _verify

def memberships(labels, target):
    """Parameterize the preimages of target by independent kernel generators."""
    basis = {}
    kernel = []
    for j, column in enumerate(labels):
        coefficients = 1 << j
        while column and column.bit_length() in basis:
            value, combination = basis[column.bit_length()]
            column ^= value
            coefficients ^= combination
        if column:
            basis[column.bit_length()] = (column, coefficients)
        else:
            kernel.append(coefficients)
    particular = 0
    while target:
        if target.bit_length() not in basis:
            return
        value, combination = basis[target.bit_length()]
        target ^= value
        particular ^= combination
    for mask in range(1 << len(kernel)):
        result = particular
        for i, vector in enumerate(kernel):
            if mask & (1 << i):
                result ^= vector
        yield result


def solve(word, marks, pins, labels=None, target=0):
    n = len(marks)
    if labels is None:
        labels = [0]*n
    if len(labels) != n or any(a not in (0,1) for a in marks):
        raise ValueError("expected labels and binary marks")
    if any(v < 0 for v in labels) or target < 0:
        raise ValueError("negative syndrome mask")
    if any(i not in range(n) or b not in (0,1) for i,b in pins.items()):
        raise ValueError("invalid pin")
    visits = [[] for _ in range(n)]
    for j,i in enumerate(word):
        if i not in range(n):
            raise ValueError("unknown chord")
        visits[i].append(j)
    if any(len(pair) != 2 for pair in visits):
        raise ValueError("expected two visits to every chord")
    if not n:
        return set() if not target else None
    order, edges, signs, _ = _gadget(word, marks, labels)
    free = [i for i in range(n) if i not in pins and labels[i]]
    relevant = list(pins) + free
    residual = target
    for i,value in pins.items():
        if value:
            residual ^= labels[i]
    def configurations():
        for mask in memberships([labels[i] for i in free], residual):
            fixed = dict(pins)
            fixed.update((i, (mask >> j) & 1) for j,i in enumerate(free))
            for rest in product((0,1), repeat=max(0,len(relevant)-1)):
                # Complementing every arc bit preserves every membership and guard.
                incoming = (0,) + rest
                ports = {}
                for a,i in zip(incoming, relevant):
                    j = visits[i][0]
                    ports[2*j] = a
                    ports[2*j+1] = a ^ (1-fixed[i])
                yield ports
    for ports in configurations():
        graph = nx.Graph()
        graph.add_nodes_from(range(order))
        for a,b,_ in edges:
            if a in ports and ports[a] != (4*n <= b < 6*n):
                continue
            if b in ports and ports[b] != (4*n <= a < 6*n):
                continue
            graph.add_edge(a,b)
        matching = nx.max_weight_matching(graph, maxcardinality=True)
        if 2*len(matching) != order:
            continue
        partner = {v:w for a,b in matching for v,w in ((a,b),(b,a))}
        f = [(4*n <= partner[2*j+1] < 6*n) ^ (signs[2*j+1] < 0)
             for j in range(len(word))]
        S = {i for i,(j,_) in enumerate(visits) if f[j] ^ f[j-1]}
        assert all((i in S) == value for i,value in pins.items())
        assert _verify(S, visits, marks, labels, target)
        return S
    return None
