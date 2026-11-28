"""Classify demand-hit indicators on simple bipartite perfect matchings."""
import networkx as nx


def _add(rows, word):
    while word:
        j = word.bit_length()-1
        if j not in rows:
            rows[j] = word
            return True
        word ^= rows[j]
    return False


def _hull(n, edges, live, forced=None):
    """Return one matching and independent actual single-cycle toggles."""
    fixed = None if forced is None else edges[forced]
    left = [i for i in range(n) if fixed is None or i != fixed[0]]
    graph = nx.Graph()
    graph.add_nodes_from(left)
    graph.add_nodes_from(n+j for j in range(n) if fixed is None or j != fixed[1])
    for e in live:
        u,v = edges[e]
        if fixed is None or (u != fixed[0] and v != fixed[1]):
            graph.add_edge(u,n+v,edge=e)
    # Unit-capacity integral flow gives a matching without enumerating witnesses.
    flow_graph = nx.DiGraph()
    for u in left:
        flow_graph.add_edge(-1,u,capacity=1)
    for v in graph:
        if v >= n:
            flow_graph.add_edge(v,-2,capacity=1)
    flow_graph.add_nodes_from((-1,-2))
    for u in left:
        for v in graph[u]:
            flow_graph.add_edge(u,v,capacity=1)
    value, flow = nx.maximum_flow(flow_graph,-1,-2,flow_func=nx.algorithms.flow.edmonds_karp)
    if value != len(left):
        return None
    mate, chosen = {}, {}
    for u in left:
        v = next(v for v in graph[u] if flow[u][v])
        mate[v], chosen[u] = u,graph[u][v]["edge"]
    base = sum(1 << e for e in chosen.values())
    if forced is not None:
        base |= 1 << forced
    digraph = nx.DiGraph()
    digraph.add_nodes_from(left)
    for u in left:
        for v in graph[u]:
            w = mate[v]
            if w != u:
                digraph.add_edge(u,w,edge=graph[u][v]["edge"])
    rows, directions = {}, []
    for comp in nx.strongly_connected_components(digraph):
        if len(comp) < 2:
            continue
        sub = digraph.subgraph(comp)
        r = min(comp)
        go = nx.single_source_shortest_path(sub,r)
        back = nx.single_source_shortest_path(sub.reverse(copy=False),r)

        def cycles(walk):
            stack = []
            at = {}
            for v in walk:
                if v not in at:
                    at[v] = len(stack)
                    stack.append(v)
                    continue
                i = at[v]
                cycle = stack[i:] + [v]
                delta = 0
                for a,b in zip(cycle,cycle[1:]):
                    delta ^= (1 << chosen[a]) | (1 << sub[a][b]["edge"])
                if _add(rows,delta):
                    directions.append(delta)
                for a in stack[i+1:]:
                    del at[a]
                del stack[i+1:]

        for u in sub:
            cycles(go[u] + list(reversed(back[u]))[1:])
        for u,v in sub.edges:
            cycles(go[u] + list(reversed(back[v])))
    return base, tuple(directions)


def classify(n_left, n_right, edges, demand):
    """Zero-based shores/edge IDs. Affine hit = parity(mask & matching) XOR constant."""
    if any(type(n) is not int or n < 0 for n in (n_left,n_right)):
        raise ValueError("invalid shore size")
    edges = tuple(tuple(e) for e in edges)
    if any(len(e)!=2 or any(type(x) is not int for x in e) or
           not (0 <= e[0] < n_left and 0 <= e[1] < n_right) for e in edges):
        raise ValueError("invalid edge")
    if len(set(edges)) != len(edges):
        raise ValueError("parallel edges are unsupported")
    requested = set()
    for e in demand:
        if type(e) is not int or not 0 <= e < len(edges):
            raise ValueError("invalid demand")
        requested.add(e)
    demand = requested
    live = tuple(range(len(edges)))
    if n_left != n_right or n_left > len(edges):
        return dict(status="empty")
    full = _hull(n_left, edges, live)
    if full is None:
        return dict(status="empty")
    base, directions = full
    arity = len(edges)
    equations = {}

    def impose(coeff, bit):
        row = coeff << 1 | bit
        while row > 1:
            j = row.bit_length()-1
            if j not in equations:
                equations[j] = row
                return True
            row ^= equations[j]
        return row == 0

    def constant_on(hull, value):
        if hull is None:
            return True
        m, ds = hull
        return impose(m | (1 << arity),value) and all(impose(d,0) for d in ds)

    avoid = _hull(n_left, edges, [i for i in live if i not in demand])
    valid = constant_on(avoid,0)
    for i in sorted(demand):
        if not valid:
            break
        valid = constant_on(_hull(n_left,edges,live,forced=i),1)
    result = dict(base=base, directions=directions)
    if not valid:
        return dict(status="nonaffine", **result)
    solution = 0
    for j,row in sorted(equations.items()):
        if ((row >> 1) & solution).bit_count() % 2 != (row & 1):
            solution |= 1 << (j-1)
    return dict(status="affine", constant=solution >> arity, mask=solution & ((1 << arity)-1),
                **result)
