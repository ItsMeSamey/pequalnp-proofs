"""Exact native even-support solver on certified flexible components.

solve(graph, pins, branch=None, rank_cap=None) uses symmetric adjacency sets on
vertices 0,...,n-1. Returns (status, original vertex set or None). UNKNOWN
reports a failed certificate or an optional exponent policy. A supplied branch
set must contain every pin. No rank limit is imposed by default.
"""
from collections import deque

from flexible_chain_control import forest_lift, parity_support, subsets
from original_dag_quadratic import gauss


def components(vertices, neighbors):
    unseen = set(vertices)
    while unseen:
        root = next(iter(unseen))
        part = {root}
        unseen.remove(root)
        queue = [root]
        for v in queue:
            for w in neighbors[v]:
                if w in unseen:
                    unseen.remove(w)
                    part.add(w)
                    queue.append(w)
        yield part


def build_quotient(graph, branch):
    direct = [(u, v) for u in branch for v in graph[u] if u < v and v in branch]
    paths = []
    for part in components(set(range(len(graph))) - branch, graph):
        attachment = {}
        for v in part:
            for w in graph[v] & branch:
                attachment.setdefault(w, set()).add(v)
        if len(attachment) > 2:
            return None
        if len(attachment) < 2:
            continue
        (u, starts), (v, ends) = attachment.items()
        back = {w: None for w in starts}
        queue = deque(starts)
        while queue:
            w = queue.popleft()
            if w in ends:
                break
            for z in graph[w]:
                if z in part and z not in back:
                    back[z] = w
                    queue.append(z)
        interior = []
        while w is not None:
            interior.append(w)
            w = back[w]
        paths.append((u, v, interior))
    return direct, paths


def certified_rows(branch, direct, paths, pins):
    links = {v: set() for v in branch}
    for u, v, _ in paths:
        links[u].add(v)
        links[v].add(u)
    groups = list(components(branch, links))
    group_id = {v: i for i, part in enumerate(groups) for v in part}
    crossing = [(u, v) for u, v in direct if group_id[u] != group_id[v]]
    exposed = {v for edge in crossing for v in edge}
    fixed = set(pins)
    for part in groups:
        if all(len(links[v]) == len(part) - 1 for v in part):
            continue
        allowed = part - (exposed - pins)
        for backbone in components(allowed, links):
            covered = set(backbone)
            for v in backbone:
                covered.update(links[v])
            if covered == part:
                fixed.update(backbone)
                break
        else:
            return None
    rows = [set() for _ in groups]
    for u, v in crossing:
        term = (0 if u in fixed else 1 << u) | (0 if v in fixed else 1 << v)
        rows[group_id[u]].symmetric_difference_update((term,))
        rows[group_id[v]].symmetric_difference_update((term,))
    return rows, fixed


def basis(rows):
    pivots = {}
    for source in rows:
        row = set(source)
        while row:
            pivot = max(row)
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return list(pivots.values())


def specialize(rows, bit, value):
    result = []
    for row in rows:
        child = set()
        for term in row:
            if term & bit == 0 or value:
                child.symmetric_difference_update((term & ~bit,))
        result.append(child)
    return basis(result)


def has_pattern(rows, free):
    if {0} in rows:
        return False
    total = 0
    poly = set()
    for step in range(1 << len(rows)):
        if step:
            poly ^= rows[(step & -step).bit_length() - 1]
        total += gauss(poly, free)
    return total > 0


def solve(graph, pins, branch=None, rank_cap=None):
    n = len(graph)
    pins = set(pins)
    if any(v < 0 or v >= n for v in pins):
        raise ValueError("pin outside graph")
    for u, adjacent in enumerate(graph):
        if any(v == u or v < 0 or v >= n or u not in graph[v] for v in adjacent):
            raise ValueError("expected loopless symmetric adjacency sets")
    if branch is None:
        branch = pins | {v for v, adjacent in enumerate(graph) if len(adjacent) != 2}
    else:
        branch = set(branch)
        if not pins <= branch or any(v < 0 or v >= n for v in branch):
            raise ValueError("branch sites must include the pins and belong to the graph")
    quotient = build_quotient(graph, branch)
    if quotient is None:
        return "UNKNOWN", None
    direct, paths = quotient
    lift, _ = forest_lift(branch, direct, paths)
    if lift is not None:
        return "YES", lift
    ends = {v for edge in direct for v in edge} - pins
    enumerate_ends = len(ends) <= 2 * len(pins) and (rank_cap is None or len(ends) <= rank_cap)
    certified = certified_rows(branch, direct, paths, pins)
    if certified is not None:
        rows, occupied = certified
        rows = basis(rows)
        if rank_cap is not None and len(rows) > rank_cap:
            certified = None
    if enumerate_ends and (certified is None or len(ends) < len(rows)):
        for chosen in subsets(ends):
            lift, _ = forest_lift((branch - ends) | chosen, direct, paths)
            if lift is not None:
                return "YES", lift
        return "NO", None
    if certified is None:
        return "UNKNOWN", None
    free = sum(1 << v for v in branch - occupied)
    if not has_pattern(rows, free):
        return "NO", None
    while free:
        bit = free & -free
        free ^= bit
        child = specialize(rows, bit, False)
        if has_pattern(child, free):
            rows = child
        else:
            occupied.add(bit.bit_length() - 1)
            rows = specialize(rows, bit, True)
    lift, _ = forest_lift(occupied, direct, paths)
    if lift is None or not pins <= lift or not parity_support(graph, lift):
        raise AssertionError("failed original witness reconstruction")
    return "YES", lift
