"""Gain-target feasibility on certified two-dimensional vertex charts.
probe(graph,target) returns (SAT/UNSAT/UNKNOWN, original witness or None,
propagated root domains). Exact whenever all residual domains have size <=2.
"""
from itertools import product
from gain_graph import pairing
from quadratic_target import apply_basis, insert, reduce_vector

PALETTE = (1, 2, 3)
IDENTITY = (0, 1, 2, 3)


def transport(matrix):
    if not 0 <= matrix < 16:
        raise ValueError("invalid matrix")
    image = [0]
    for a in PALETTE:
        zeros = [b for b in PALETTE if not pairing(matrix, a, b)]
        if len(zeros) != 1:
            raise ValueError("singular matrix")
        image.append(zeros[0])
    if len(set(image)) != 4:
        raise ValueError("singular matrix")
    return tuple(image)


def binary_solution(domains, relations):
    choices = [(tuple(sorted(d)) * 2)[:2] for d in domains]
    adj = [[] for _ in range(2 * len(domains))]
    back = [[] for _ in adj]
    for (i, j), allowed in relations.items():
        for a, b in product(range(2), repeat=2):
            if (choices[i][a], choices[j][b]) not in allowed:
                for u, v in ((2*i+a, 2*j+(1-b)), (2*j+b, 2*i+(1-a))):
                    adj[u].append(v)
                    back[v].append(u)
    order = []
    seen = set()
    for u in range(len(adj)):
        if u in seen:
            continue
        stack = [(u, False)]
        while stack:
            v, leaving = stack.pop()
            if leaving:
                order.append(v)
            elif v not in seen:
                seen.add(v)
                stack.append((v, True))
                stack.extend((w, False) for w in adj[v] if w not in seen)
    component = [-1] * len(adj)
    for priority, u in enumerate(reversed(order)):
        if component[u] >= 0:
            continue
        stack = [u]
        component[u] = priority
        while stack:
            for v in back[stack.pop()]:
                if component[v] < 0:
                    component[v] = priority
                    stack.append(v)
    if any(component[2*i] == component[2*i+1] for i in range(len(domains))):
        return None
    return tuple(choices[i][int(component[2*i+1] > component[2*i])] for i in range(len(domains)))


def solve_edges(n, edges, target):
    edges = tuple(edges)
    if n < 0 or not 0 <= target < 1 << len(edges):
        raise ValueError("invalid dimension or edge target")
    active = set()
    zeros = [[] for _ in range(n)]
    ones = []
    for j, (u, v, matrix) in enumerate(edges):
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError("invalid vertex")
        gain = transport(matrix)
        if (target >> j) & 1:
            active.update((u, v))
            ones.append((u, v, gain))
        else:
            zeros[u].append((v, gain))
            zeros[v].append((u, tuple(gain.index(c) for c in range(4))))

    owner = [-1] * n
    path = [None] * n
    domains = []
    for root in sorted(active):
        if owner[root] >= 0:
            continue
        i = len(domains)
        possible = set(PALETTE)
        domains.append(possible)
        owner[root], path[root] = i, IDENTITY
        stack = [root]
        while stack:
            u = stack.pop()
            for v, gain in zeros[u]:
                if v not in active:
                    continue
                implied = tuple(gain[c] for c in path[u])
                if owner[v] < 0:
                    owner[v], path[v] = i, implied
                    stack.append(v)
                else:
                    possible.intersection_update(c for c in PALETTE if path[v][c] == implied[c])

    relations = {}
    for u, v, gain in ones:
        i, j = owner[u], owner[v]
        if i == j:
            domains[i].intersection_update(c for c in PALETTE if path[v][c] != gain[path[u][c]])
        else:
            allowed = {(a, b) for a, b in product(PALETTE, repeat=2)
                       if path[v][b] != gain[path[u][a]]}
            if i > j:
                i, j = j, i
                allowed = {(b, a) for a, b in allowed}
            if (i, j) in relations:
                relations[i, j].intersection_update(allowed)
            else:
                relations[i, j] = allowed
    changed = True
    while changed:
        changed = False
        for (i, j), allowed in relations.items():
            supported = [(a, b) for a, b in allowed if a in domains[i] and b in domains[j]]
            for k, vals in ((i, {a for a, _ in supported}), (j, {b for _, b in supported})):
                if vals != domains[k]:
                    domains[k] = vals
                    changed = True
    lists = tuple(tuple(sorted(d)) for d in domains)
    if any(not d for d in domains):
        return "UNSAT", None, lists
    # After zero-edge contraction several one-edges can constrain the same
    # pair. Charge their joint maximum number of forbidden colors, conditional
    # on one neighbor, rather than counting that neighbor only once.
    neighbors = [[] for _ in domains]
    for (i, j), allowed in relations.items():
        for u, v, ok in ((i, j, allowed), (j, i, {(b, a) for a, b in allowed})):
            loss = max(sum((a, b) not in ok for a in domains[u]) for b in domains[v])
            neighbors[u].append((v, ok, loss))
    core = set(range(len(domains)))
    peeled = []
    for _ in range(len(domains)):
        u = next((i for i in sorted(core) if len(domains[i]) >
                  sum(loss for v, _, loss in neighbors[i] if v in core)), None)
        if u is None:
            break
        core.remove(u)
        peeled.append(u)
    ordered = sorted(core)
    index = {u: i for i, u in enumerate(ordered)}
    restricted = {(index[i], index[j]): ok for (i, j), ok in relations.items()
                  if i in core and j in core}
    assignment = binary_solution([domains[u] for u in ordered], restricted)
    if assignment is None:
        return ("UNKNOWN" if any(len(domains[u]) > 2 for u in core) else "UNSAT"), None, lists
    colors = dict(zip(ordered, assignment))
    for u in reversed(peeled):
        colors[u] = next(a for a in sorted(domains[u])
                         if all((a, colors[v]) in ok for v, ok, _ in neighbors[u] if v in colors))
    codes = tuple(0 if owner[u] < 0 else path[u][colors[owner[u]]] for u in range(n))
    value = sum(pairing(mat, codes[u], codes[v]) << j for j, (u, v, mat) in enumerate(edges))
    if value != target:
        raise ArithmeticError("invalid gain witness")
    return "SAT", codes, lists


def probe(graph, target):
    rows = {}
    for j, (_, _, e, _) in enumerate(graph.edges):
        if not insert(e, 1 << j, rows):
            raise ValueError("dependent chart output vectors")
    if target < 0:
        raise ValueError("negative target")
    residue, goal = reduce_vector(target ^ graph.output_offset, rows)
    if residue:
        return "UNSAT", None, ()
    edges = [(u, v, mat) for u, v, e, mat in graph.edges]
    status, codes, lists = solve_edges(len(graph.planes), edges, goal)
    if codes is None:
        return status, None, lists
    witness = graph.shift
    value = graph.output_offset
    for plane, code in zip(graph.planes, codes):
        witness ^= apply_basis(plane, code)
    for u, v, e, mat in graph.edges:
        if pairing(mat, codes[u], codes[v]):
            value ^= e
    if value != target:
        raise ArithmeticError("invalid ambient output lift")
    return status, witness, lists


def check():
    from itertools import combinations
    from random import Random
    from gain_graph import recover
    from quadratic_centroid import independent
    from quadratic_target import interpolate
    rng = Random(389)
    cases = 0
    for _ in range(80):
        n = rng.randrange(1, 5)
        edges = [(rng.randrange(n), rng.randrange(n), rng.choice((6,7,9,11,13,14)))
                 for _ in range(rng.randrange(7))]
        image = {sum(pairing(mat, x[u], x[v]) << j for j, (u, v, mat) in enumerate(edges))
                 for x in product(range(4), repeat=n)}
        for t in range(1 << len(edges)):
            st, witness, lists = solve_edges(n, edges, t)
            if st == "SAT":
                assert t in image and witness is not None
            elif st == "UNSAT":
                assert t not in image
            else:
                assert any(len(d) == 3 for d in lists)
            cases += 1
    # No fixed color for a three-cycle holonomy on the active zero triangle.
    zero_cycle = [(0, 1, 6), (1, 2, 6), (2, 0, 11)]
    pendants = [(i, i+3, 6) for i in range(3)]
    assert solve_edges(6, zero_cycle + pendants, 56)[0] == "UNSAT"
    # Each transposition loop permits 1,2; odd cycle fails 2-SAT although
    # unary arc consistency keeps both colors at every vertex.
    for n in (3, 4):
        edges = [(i, i, 9) for i in range(n)] + [(i, (i+1)%n, 6) for i in range(n)]
        status, _, domains = solve_edges(n, edges, (1 << len(edges))-1)
        assert all(d == (1, 2) for d in domains)
        assert status == ("UNSAT" if n == 3 else "SAT")
    triangle = [(i, j, 6) for i, j in combinations(range(3), 2)]
    assert solve_edges(3, triangle, 7)[0] == "SAT"  # three colors, all peeled
    # Dense affine recoding of a genuine twisted five-cycle.
    def basis(k):
        cols = ()
        while len(cols) < k:
            cols = independent((*cols, rng.randrange(1 << k)))
        return cols
    ib, ob = basis(10), basis(5)
    def original(x):
        z = apply_basis(ib, x ^ 285)
        v = [(z >> (2*i)) & 3 for i in range(5)]
        return 13 ^ apply_basis(ob, sum(pairing(6 if i < 4 else 11, v[i], v[(i+1)%5]) << i
                                         for i in range(5)))
    graph = recover(10, 5, *interpolate(original, 10))
    assert graph is not None
    image = {original(x) for x in range(1024)}
    for target in range(32):
        status, witness, _ = probe(graph, target)
        assert status == ("SAT" if target in image else "UNSAT")
        assert witness is None or original(witness) == target
    print(f"{cases} small targets, strict holonomy/2SAT/peeling and 32 recoded targets passed")


if __name__ == "__main__":
    check()
