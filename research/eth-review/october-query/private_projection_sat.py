"""SAT decision by exact local projection onto binary constraints and SCCs."""
from itertools import combinations, product


def literal_true(lit, assignment):
    return bool(assignment[abs(lit)]) == (lit > 0)


def recognize_pairs(rows):
    """Recognize disjoint fresh-pair four-clause blocks by physical incidences."""
    incidence = {}
    for i, row in enumerate(rows):
        for lit in row:
            incidence.setdefault(abs(lit), set()).add(i)
    by_scope = {}
    for variable, ids in incidence.items():
        if len(ids) == 4:
            by_scope.setdefault(tuple(sorted(ids)), []).append(variable)
    selected = []
    used = set()
    for ids, variables in by_scope.items():
        if used.intersection(ids):
            continue
        for p, q in combinations(variables, 2):
            signs = {(p in rows[i], q in rows[i]) for i in ids}
            if len(signs) == 4:
                selected.append((p, q))
                used.update(ids)
                break
    return selected


def binary_sat(clauses):
    graph, reverse = {}, {}
    for row in clauses:
        if not row:
            return False
        a, b = row[0], row[-1]
        for x,y in ((-a,b),(-b,a)):
            graph.setdefault(x, []).append(y)
            reverse.setdefault(y, []).append(x)
    vertices = set(graph) | set(reverse)
    done = set()
    order = []
    for v in vertices:
        if v in done:
            continue
        stack = [(v, False)]
        while stack:
            x, leaving = stack.pop()
            if leaving:
                order.append(x)
            elif x not in done:
                done.add(x)
                stack.append((x, True))
                stack.extend((y,False) for y in graph.get(x, ()))
    component = {}
    for root in reversed(order):
        if root in component:
            continue
        stack = [root]
        while stack:
            x = stack.pop()
            if x not in component:
                component[x] = root
                stack.extend(reverse.get(x, ()))
    return all(component[v] != component[-v] for v in vertices)


def decide(clauses, private=None):
    """Return (SAT Boolean, 'binary' or 'core'); empty unused variables irrelevant."""
    rows = [tuple(dict.fromkeys(row)) for row in clauses]
    if any(not isinstance(lit,int) or lit == 0 for row in rows for lit in row):
        raise ValueError("invalid signed variable")
    rows = [row for row in rows if not any(-lit in row for lit in row)]
    blocks = list(recognize_pairs(rows) if private is None else private)
    owners = {}
    for i, block in enumerate(blocks):
        for x in block:
            if x in owners or x <= 0:
                raise ValueError("private blocks must be disjoint positive variables")
            owners[x] = i
    groups = [[] for _ in blocks]
    for row in rows:
        ids = {owners[abs(lit)] for lit in row if abs(lit) in owners}
        if len(ids)>1:
            raise ValueError("clause crosses two private blocks")
        if ids:
            groups[ids.pop()].append(row)
        else:
            groups.append([row])
    tables, constraints = [], []
    is_binary = True
    for i, group in enumerate(groups):
        internal = blocks[i] if i<len(blocks) else ()
        interface = sorted({abs(lit) for row in group for lit in row}-set(internal))
        allowed = set()
        for state in product((0,1),repeat=len(interface)):
            values = dict(zip(interface,state))
            for hidden in product((0,1),repeat=len(internal)):
                values.update(zip(internal,hidden))
                if all(any(literal_true(lit,values) for lit in row) for row in group):
                    allowed.add(state)
                    break
        if not allowed:
            return False, 'binary'
        tables.append((interface,allowed))
        local = []
        for k in (1,2):
            for positions in combinations(range(len(interface)),k):
                realized = {tuple(a[j] for j in positions) for a in allowed}
                for bits in product((0,1), repeat=k):
                    if bits not in realized:
                        local.append(tuple(-interface[j] if b else interface[j]
                                           for j,b in zip(positions,bits)))
        for state in product((0,1),repeat=len(interface)):
            if state in allowed:
                continue
            values=dict(zip(interface,state))
            if all(any(literal_true(lit,values) for lit in row) for row in local):
                is_binary=False
                break
        constraints.extend(local)
    if is_binary:
        return binary_sat(constraints), 'binary'
    core=sorted({x for xs,_ in tables for x in xs})
    for state in product((0,1),repeat=len(core)):
        values=dict(zip(core,state))
        if all(tuple(values[x] for x in xs) in allowed for xs,allowed in tables):
            return True,'core'
    return False,'core'
