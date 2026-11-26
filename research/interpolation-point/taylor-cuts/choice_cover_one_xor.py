"""Disjoint signed choice covers, pair conflicts, and one parity equation.

SAT returns a bit word on the original variables; UNSAT returns None. Errors
outside the recognized presentation raise ValueError. Input uses signed DIMACS
literals. The cover clauses are designated by their indices, including small
covers indistinguishable syntactically from binary conflict clauses.
"""
from collections import deque
from dataclasses import dataclass


@dataclass(frozen=True)
class Option:
    resource: int
    event: int  # 0 denotes a dummy option; real events use 1-based variable ids
    parity: int


def odd_cycle(adj):
    """Return (row, option) on a simple directed odd cycle, loops included."""
    for root in range(len(adj)):
        start, goal = (root, 0), (root, 1)
        parent = {start: None}
        queue = deque([start])
        while queue and goal not in parent:
            u, z = state = queue.popleft()
            for v, weight, option in adj[u]:
                child = (v, z ^ weight)
                if child not in parent:
                    parent[child] = state, (u, v, weight, option)
                    queue.append(child)
        if goal not in parent:
            continue
        walk = []
        state = goal
        while state != start:
            state, edge = parent[state]
            walk.append(edge)
        walk.reverse()
        while True:
            visits = {}
            for j, (u, _, _, _) in enumerate(walk):
                if u in visits:
                    i = visits[u]
                    parity = sum(e[2] for e in walk[i:j]) % 2
                    walk = walk[i:j] if parity else walk[:i] + walk[j:]
                    break
                visits[u] = j
            else:
                return [(u, option) for u, _, _, option in walk]
    return None


def prepare(n, clauses, covers, equations):
    """Return padded option rows, target mask, free-variable masks and events."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("invalid variable count")
    clauses = [tuple(dict.fromkeys(c)) for c in clauses]
    equations = [(tuple(row), rhs) for row, rhs in equations]
    if any(rhs not in (0, 1) for _, rhs in equations):
        raise ValueError("invalid parity")
    for row in clauses + [row for row, _ in equations]:
        if any(not isinstance(l,int) or not 1<=abs(l)<=n for l in row):
            raise ValueError("invalid literal")
    covers=tuple(covers)
    if len(set(covers))!=len(covers) or any(i<0 or i>=len(clauses) for i in covers):
        raise ValueError("invalid covers")
    group={}; signed={}; group_vars=[]
    for g,i in enumerate(covers):
        vs=[]
        for lit in clauses[i]:
            v=abs(lit)
            if v in group:raise ValueError("cover scopes must be disjoint")
            group[v]=g; signed[v]=lit; vs.append(v)
        group_vars.append(vs)
    within=set(); cross={v:set() for v in group}
    cover_set=set(covers)
    for i,c in enumerate(clauses):
        if i in cover_set:continue
        if len(c)!=2 or any(signed.get(abs(l)) != -l for l in c):
            raise ValueError("expected a pair of negated events")
        u,v=sorted(map(abs,c))
        if group[u]==group[v]:within.add((u,v))
        else:cross[u].add(v);cross[v].add(u)
    for vs in group_vars:
        if any(tuple(sorted((u,v))) not in within for j,u in enumerate(vs) for v in vs[j+1:]):
            raise ValueError("cover lacks an at-most-one clause")
    resource={}
    for seed in group:
        if seed in resource:continue
        stack=[seed]; comp={seed}
        while stack:
            u=stack.pop()
            for v in cross[u]-comp:
                comp.add(v);stack.append(v)
        if any(v not in cross[u] for u in comp for v in comp if group[u]!=group[v]):
            raise ValueError("cross-conflict component is not complete multipartite")
        rid=seed
        for v in comp:resource[v]=rid
    target = 0
    masks = {}
    for j, (literals, rhs) in enumerate(equations):
        target ^= rhs << j
        for lit in literals:
            v = abs(lit)
            masks[v] = masks.get(v, 0) ^ (1 << j)
            if lit < 0:
                target ^= 1 << j
    for v, lit in signed.items():
        if lit < 0:
            target ^= masks.get(v, 0)
    free = [(v, mask) for v, mask in sorted(masks.items()) if v not in signed and mask]
    resources = sorted(set(resource.values()))
    if len(resources) < len(covers) or any(not vs for vs in group_vars):
        return None
    options = [[Option(resource[v], v, masks.get(v, 0)) for v in vs] for vs in group_vars]
    for _ in range(len(resources) - len(covers)):
        options.append([Option(r, 0, 0) for r in resources])
    return options, target, free, signed


def initial_matching(options):
    owner={}; chosen={}
    for root in range(len(options)):
        queue=deque([root]); previous={root:None}; touched=set(); found=False
        while queue and not found:
            u=queue.popleft()
            for opt in options[u]:
                r=opt.resource
                if r in touched:continue
                touched.add(r)
                if r not in owner:
                    while True:
                        chosen[u]=opt;owner[opt.resource]=u
                        if previous[u] is None:break
                        u,opt=previous[u]
                    found=True
                    break
                v=owner[r]
                if v not in previous:
                    previous[v]=u,opt
                    queue.append(v)
        if not found:return None
    return [chosen[i] for i in range(len(options))]


def decode(chosen, signed, free, free_word, clauses, equations):
    active = {o.event for o in chosen if o.event}
    answer = sum(1 << (v-1) for v in signed if (v in active) ^ (signed[v] < 0))
    for j, (v, _) in enumerate(free):
        if free_word >> j & 1:
            answer |= 1 << (v-1)
    def value(lit):
        return bool(answer >> (abs(lit)-1) & 1) ^ (lit < 0)
    if not all(any(value(l) for l in clause) for clause in clauses):
        raise AssertionError("decoded matching violates original CNF")
    if not all(sum(value(l) for l in row) % 2 == rhs for row,rhs in equations):
        raise AssertionError("decoded matching violates original XOR")
    return answer


def solve(n, clauses, covers, xor_literals, rhs):
    clauses = tuple(tuple(c) for c in clauses)
    equations = [(tuple(xor_literals), rhs)]
    problem = prepare(n, clauses, covers, equations)
    if problem is None:
        return None
    options, target, free, signed = problem
    chosen = initial_matching(options)
    if chosen is None:
        return None
    mismatch = (sum(o.parity for o in chosen) % 2) ^ target
    if mismatch and not free:
        owner = {opt.resource:i for i,opt in enumerate(chosen)}
        adj = [[(owner[o.resource],o.parity ^ chosen[u].parity,o) for o in row]
               for u,row in enumerate(options)]
        cycle = odd_cycle(adj)
        if cycle is None:
            return None
        for u,opt in cycle:
            chosen[u] = opt
    return decode(chosen, signed, free, int(bool(free and mismatch)), clauses, equations)
