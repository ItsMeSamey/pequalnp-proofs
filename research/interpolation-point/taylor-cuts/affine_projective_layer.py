"""Projective-line choices for blocks over F_2. Each column of a matrix block
is a two-bit vector, stored at bit positions (0,1) and (2,3) respectively.
"""
from itertools import combinations


def apply_block(block, vector):
    return ((block & 3) if vector & 1 else 0) ^ ((block >> 2) if vector & 2 else 0)


def _two_sat(atom_count, clauses):
    """Kosaraju SCCs. Literal 2*i+1 means atom i is true."""
    g = [[] for _ in range(2 * atom_count)]
    rev = [[] for _ in g]
    for a, b in clauses:
        for u, v in ((a ^ 1, b), (b ^ 1, a)):
            g[u].append(v)
            rev[v].append(u)
    seen = set()
    order = []
    for start in range(len(g)):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(g[start]))]
        while stack:
            u, edges = stack[-1]
            v = next(edges, None)
            if v is None:
                order.append(u)
                stack.pop()
            elif v not in seen:
                seen.add(v)
                stack.append((v, iter(g[v])))
    component = [-1] * len(g)
    for label, start in enumerate(reversed(order)):
        if component[start] != -1:
            continue
        component[start] = label
        stack = [start]
        while stack:
            for v in rev[stack.pop()]:
                if component[v] == -1:
                    component[v] = label
                    stack.append(v)
    if any(component[i] == component[i+1] for i in range(0,len(g),2)):
        return None
    return [component[i+1] > component[i] for i in range(0,len(g),2)]


def recognize(blocks, column_count=None):
    """Return (gate_lines, block_lines) or None. Rows are gates.
    For each entry A, the image of its gate line must be zero or its block line.
    Supply column_count when an empty matrix has a prescribed number of columns.
    """
    nr = len(blocks)
    nc = (len(blocks[0]) if nr else 0) if column_count is None else column_count
    if nc < 0 or any(len(row) != nc for row in blocks):
        raise ValueError("invalid matrix dimensions")
    eq = [[] for _ in range(nr+nc)]
    choices = []
    for i, row in enumerate(blocks):
        for j, block in enumerate(row, nr):
            if not isinstance(block, int) or not 0 <= block < 16:
                raise ValueError("expected a four-bit block")
            if not block:
                continue
            image = [apply_block(block, x) for x in range(4)]
            if 0 in image[1:]:
                choices.append(((i,image.index(0,1)), (j,max(image))))
            else:
                eq[i].append((j,image))
                eq[j].append((i,[image.index(x) for x in range(4)]))

    root = [-1] * len(eq)
    potential = [None] * len(eq)
    domains = {}
    lines = (1,2,3)
    for start in range(len(eq)):
        if root[start] != -1:
            continue
        domain = set(lines)
        domains[start] = domain
        potential[start] = list(range(4))
        root[start] = start
        stack = [start]
        while stack:
            u = stack.pop()
            for v, perm in eq[u]:
                proposed = [perm[x] for x in potential[u]]
                if root[v] == -1:
                    root[v] = start
                    potential[v] = proposed
                    stack.append(v)
                else:
                    domain.intersection_update(x for x in lines if potential[v][x] == proposed[x])
        if not domain:
            return None

    atoms = {(r,x): i for i,(r,x) in enumerate((r,x) for r in domains for x in sorted(domains[r]))}
    clauses = []
    for r, domain in domains.items():
        for a,b in combinations(domain,2):
            clauses.append((2*atoms[r,a], 2*atoms[r,b]))
    for alternatives in choices:
        possible = []
        for u, value in alternatives:
            r = root[u]
            a = potential[u].index(value)
            if a in domains[r]:
                possible.append(2*atoms[r,a]+1)
        if not possible:
            return None
        clauses.append((possible[0], possible[-1]))
    truth = _two_sat(len(atoms),clauses)
    if truth is None:
        return None
    chosen = {r:min(domain) for r,domain in domains.items()}
    for (r,x),i in atoms.items():
        if truth[i]:
            chosen[r] = x
    solution = [potential[u][chosen[r]] for u,r in enumerate(root)]
    return solution[:nr], solution[nr:]
