"""SCC reachability index for batches of unit-conditioned NAND row probes."""
from itertools import combinations, product
from corridor_nand import _hull, _net, _replay, _rows, _sat
from row_csp import _prepare
from ordered_row_csp import ordered_assignment


class PinIndex:
    """Index a fixed DIMACS 2-CNF. compatible() takes signed integer units."""
    def __init__(self, variables, rows):
        if type(variables) is not int or variables < 0:
            raise ValueError("invalid variable count")
        self.variables = variables
        self.consistent = True
        graph = [set() for _ in range(2*variables)]
        reverse = [set() for _ in graph]
        for row in rows:
            nodes = tuple(self._node(l) for l in row)
            if len(nodes) > 2:
                raise ValueError("expected clauses of arity at most two")
            if not nodes:
                self.consistent = False
                continue
            a, b = nodes[0], nodes[-1]
            for x,y in ((a^1,b), (b^1,a)):
                graph[x].add(y)
                reverse[y].add(x)
        if not self.consistent:
            return
        seen = bytearray(len(graph))
        order = []
        for root in range(len(graph)):
            if seen[root]:
                continue
            seen[root] = 1
            stack = [(root,iter(graph[root]))]
            while stack:
                x, adj = stack[-1]
                y = next(adj,None)
                if y is None:
                    order.append(x)
                    stack.pop()
                elif not seen[y]:
                    seen[y] = 1
                    stack.append((y,iter(graph[y])))
        comp = [-1]*len(graph)
        blocks = 0
        for root in reversed(order):
            if comp[root] >= 0:
                continue
            comp[root] = blocks
            stack = [root]
            while stack:
                for y in reverse[stack.pop()]:
                    if comp[y] < 0:
                        comp[y] = blocks
                        stack.append(y)
            blocks += 1
        self.consistent = all(comp[x] != comp[x^1] for x in range(0,len(graph),2))
        if not self.consistent:
            return
        dag = [set() for _ in range(blocks)]
        for x, neighbors in enumerate(graph):
            for y in neighbors:
                if comp[x] != comp[y]:
                    dag[comp[x]].add(comp[y])
        reach = [1 << k for k in range(blocks)]
        for k in reversed(range(blocks)):
            for j in dag[k]:
                if j <= k:
                    raise AssertionError("SCC numbering not topological")
                reach[k] |= reach[j]
        self.comp, self.reach = comp, reach

    def _node(self, literal):
        if type(literal) is not int or not 1 <= abs(literal) <= self.variables:
            raise ValueError("invalid literal")
        return 2*(abs(literal)-1) + (literal < 0)

    def compatible(self, pins):
        nodes = [self._node(l) for l in pins]
        if not self.consistent:
            return False
        opposites = 0
        for x in nodes:
            opposites |= 1 << self.comp[x^1]
        return all(not (self.reach[self.comp[x]] & opposites) for x in nodes)


def _condition(n, base, tables, stats):
    while True:
        index = PinIndex(n, base)
        if not index.consistent:
            return None, index
        pending, additions = [], []
        for table in tables:
            kept = [row for row in table if index.compatible(l for l, in row)]
            stats["pruned"] += len(table)-len(kept)
            if not kept:
                return None, index
            ports = [abs(l)-1 for l, in kept[0]]
            words = [tuple(int(l > 0) for l, in row) for row in kept]
            if all(tuple((x&y)|(x&z)|(y&z) for x,y,z in zip(a,b,c)) in words
                   for a,b,c in combinations(words,3)):
                additions.append(_hull(ports,words))
            else:
                pending.append(kept)
        if not additions:
            return pending, index
        for clauses in additions:
            base.extend(clauses)
        stats["promoted"] += len(additions)
        stats["bad"] -= len(additions)
        tables = pending


def _indexed_relations(index, rows):
    domains = [list(range(len(table))) for table in rows]
    relations = [{} for _ in rows]
    masks = [[tuple(l for l, in row) for row in table] for table in rows]
    for i,j in combinations(range(len(rows)),2):
        ok = {(s,t) for s,t in product(domains[i],domains[j])
              if index.compatible(masks[i][s]+masks[j][t])}
        if not ok:
            return None
        if len(ok) != len(domains[i])*len(domains[j]):
            relations[i][j] = ok
            relations[j][i] = {(t,s) for s,t in ok}
    return domains, relations


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None,
          mode="auto", max_bad=None):
    """Check min/median charts on the original NAND problem after row promotion."""
    gates = _net(inputs, gates)
    if mode not in ("auto", "min", "median"):
        raise ValueError("invalid chart mode")
    if max_bad is not None and (type(max_bad) is not int or max_bad < 0):
        raise ValueError("invalid cap")
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs+len(gates):
            raise ValueError("invalid wire")
        pins = tuple(pins) + ((output, 1),)
    original = _rows(inputs+len(gates), clauses, pins, equalities)
    physical, expanded, aliases, base, factors, tables = _prepare(inputs, gates, original)
    n = inputs + len(physical)
    stats = dict(initial_bad=len(tables), bad=len(tables), promoted=0, pruned=0, method=None)
    rows, index = _condition(n, base, tables, stats)
    if rows is None:
        return "unsat", stats, None
    if max_bad is not None and len(rows) > max_bad:
        return "skip", stats, None
    pairwise = _indexed_relations(index, rows)
    if pairwise is None:
        return "unsat", stats, None
    status, kind, chosen = ordered_assignment(*pairwise, mode=mode)
    stats["method"] = kind
    if status != "sat":
        return status, stats, None
    full = base.copy()
    for i, value in chosen.items():
        full.extend(rows[i][value])
    model = _sat(n, full)
    if model is None:
        raise AssertionError("compatible ordered rows failed to integrate")
    raw = model[:inputs]
    for ports, entries, traces in factors:
        word = traces[tuple(model[w] for w in ports)]
        for w, bit in zip(entries, word):
            if w < inputs:
                raw[w] = bit
    material = _replay(raw, physical)
    wires = _replay(raw, gates)
    if any(w != ((0 if v == -1 else material[expanded[v]]) ^ flip)
           for w, (v, flip) in zip(wires, aliases)):
        raise AssertionError("original wire alias failed replay")
    if any(not any(material[abs(l)-1] == (l > 0) for l in row) for row in full):
        raise AssertionError("row model failed physical replay")
    if any(not any(wires[abs(l)-1] == (l > 0) for l in row) for row in original):
        raise AssertionError("original exterior or output failed replay")
    return "sat", stats, tuple(raw)
