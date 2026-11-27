"""Find a universal forest reference for optional three-cycles on disjoint sockets."""
from itertools import combinations, product
from random import Random
import networkx as nx


def circles(p):
    seen = set()
    out = []
    for i in range(len(p)):
        if i in seen:
            continue
        walk = []
        while i not in seen:
            seen.add(i)
            walk.append(i)
            i = p[i]
        out.append(walk)
    return out


def swap(p, pairs):
    q = list(p)
    for a, b in pairs:
        q[a], q[b] = q[b], q[a]
    return q


def split_chords(p, gates):
    owner = {a: j for j, triple in enumerate(gates) for a in triple}
    selected = {}
    for walk in circles(p):
        m = len(walk)
        pos = {a: i for i, a in enumerate(walk)}
        score = [[0] * (m + 1) for _ in range(m + 1)]
        choice = {}
        for i in reversed(range(m)):
            a = walk[i]
            for end in range(i + 1, m + 1):
                best = score[i + 1][end]
                for b in gates[owner[a]] if a in owner else ():
                    j = pos.get(b, -1)
                    if i < j < end:
                        val = 1 + score[i + 1][j] + score[j + 1][end]
                        if val > best:
                            best = val
                            choice[i, end] = j
                score[i][end] = best
        todo = [(0, m)]
        while todo:
            i, end = todo.pop()
            if i >= end:
                continue
            j = choice.get((i, end))
            if j is None:
                todo.append((i + 1, end))
            else:
                selected[owner[walk[i]]] = (walk[i], walk[j])
                todo.extend([(i + 1, j), (j + 1, end)])
    if len(selected) == len(gates):
        return [selected[i] for i in range(len(gates))]
    return None


def colored_path(edges, s, t):
    if s == t:
        return []
    graph = nx.Graph()
    graph.add_nodes_from([("h", s, 0), ("h", t, 0)])
    for u, v, c, opt in edges:
        if u == v:
            continue
        for w in (u, v):
            p, m = ("p", w, c), ("m", w, c)
            graph.add_edge(p, m)
            graph.add_edge(m, ("h", w, 0))
            if w not in (s, t):
                graph.add_edge(m, ("h", w, 1))
                graph.add_edge(("h", w, 0), ("h", w, 1))
        graph.add_edge(("p", u, c), ("p", v, c), choice=(c, opt))
    matching = nx.max_weight_matching(graph, maxcardinality=True)
    if len(matching) * 2 != len(graph):
        return None
    used = nx.Graph()
    for a, b in matching:
        choice = graph[a][b].get("choice")
        if choice is not None:
            used.add_edge(a[1], b[1], choice=choice)
    path = nx.shortest_path(used, s, t)
    return [used[u][v]["choice"] for u, v in zip(path, path[1:])]


def physical(p, gates, bits):
    q = list(p)
    for (a, b, c), on in zip(gates, bits):
        if on:
            q[a], q[b], q[c] = p[b], p[c], p[a]
    return q


def solve(p, gates, s, t):
    """Return (recognized, join mask). None is a legitimate recognized NO."""
    chords = split_chords(p, gates)
    if chords is None:
        return False, None
    b = swap(p, chords)
    label = {a: i for i, walk in enumerate(circles(b)) for a in walk}
    edges = []
    for i, triple in enumerate(gates):
        for on in (False, True):
            target = [p[triple[(j + int(on)) % 3]] for j in range(3)]
            u, v = [x for x, y in zip(triple, target) if b[x] != y]
            edges.append((label[u], label[v], i, on))
    for u, v, c, _ in edges:
        if u == v or colored_path([e for e in edges if e[2] != c], u, v) is not None:
            return False, None
    path = colored_path(edges, label[s], label[t])
    if path is None:
        return True, None
    mask = [False] * len(gates)
    for c, opt in path:
        mask[c] = opt
    assert any(s in walk and t in walk for walk in circles(physical(p, gates, mask)))
    return True, mask


def brute(p, gates, s, t):
    masks = list(product((False, True), repeat=len(gates)))
    walks = [circles(physical(p, gates, mask)) for mask in masks]
    possible = any(any(s in w and t in w for w in z) for z in walks)
    states = [physical(p, gates, mask) for mask in masks]
    for chords in product(*(combinations(tr, 2) for tr in gates)):
        b = swap(p, chords)
        labels = {a: i for i, walk in enumerate(circles(b)) for a in walk}
        all_forests = True
        for state in states:
            parts = dict(labels)
            for triple in gates:
                x, y = [a for a in triple if b[a] != state[a]]
                left, right = parts[x], parts[y]
                if left == right:
                    all_forests = False
                    break
                parts = {a: left if group == right else group for a, group in parts.items()}
            if not all_forests:
                break
        if all_forests:
            return True, possible
    return False, possible


if __name__ == "__main__":
    rng = Random(936)
    good = yes = no = 0
    for n in range(1, 7):
        gates = [tuple(range(3*i, 3*i+3)) for i in range(n)]
        for _ in range(250):
            p = list(range(3*n))
            rng.shuffle(p)
            s, t = rng.sample(range(len(p)), 2)
            b, feasible = brute(p, gates, s, t)
            ok, mask = solve(p, gates, s, t)
            assert ok == b and (not ok or feasible == (mask is not None))
            good += ok
            yes += ok and feasible
            no += ok and not feasible
    print(f"1500 checked; {good} recognized, {yes} YES and {no} NO.")
