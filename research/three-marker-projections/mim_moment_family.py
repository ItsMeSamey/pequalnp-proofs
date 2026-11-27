"""Physical GF(2) moment representatives for connected spanning partitions."""
from itertools import combinations, permutations, product


def _add_independent(rows, vector):
    reduced = vector.copy()
    while reduced:
        pivot = max(reduced)
        if pivot not in rows:
            rows[pivot] = reduced
            return True
        reduced.symmetric_difference_update(rows[pivot])
    return False


def _components(sites, neighbors):
    unseen = set(sites)
    while unseen:
        seed = unseen.pop()
        component = {seed}
        frontier = [seed]
        while frontier:
            new = neighbors[frontier.pop()] & unseen
            unseen.difference_update(new)
            component.update(new)
            frontier.extend(new)
        yield component


def _layout_nodes(layout, n):
    """Flatten a binary layout without relying on Python recursion."""
    pending = [(layout, False)]
    roots = []
    nodes = []
    seen = set()
    while pending:
        node, closing = pending.pop()
        if closing:
            right = roots.pop()
            left = roots.pop()
            nodes.append((None, left, right))
        elif isinstance(node, int):
            if not 0 <= node < n or node in seen:
                raise ValueError("Invalid or repeated layout site")
            seen.add(node)
            nodes.append((node, None, None))
        else:
            if not isinstance(node, (tuple, list)) or len(node) != 2:
                raise ValueError("An internal layout node must have two children")
            pending.extend(((node, True), (node[1], False), (node[0], False)))
            continue
        roots.append(len(nodes) - 1)
    if len(seen) != n:
        raise ValueError("The layout must contain every physical site")
    return nodes


def _monomials(assignment, degree):
    entries = tuple(sorted(assignment.items()))
    return {term for size in range(min(degree,len(entries))+1)
            for term in combinations(entries,size)}


def _connectivity_features(assignment, neighbors, color_count, anchors):
    """Odd component splits by exterior-neighborhood signature."""
    sites = set(assignment)
    parity = {(0,) * (2 * color_count)}
    for color, anchor in enumerate(anchors):
        selected = [v for v in sites if assignment[v] == color]
        for component in _components(selected, neighbors):
            adjacent = set().union(*(neighbors[v] for v in component)) - sites
            mask = sum(1 << v for v in adjacent)
            allowed = (0,) if anchor in component else (0, 1)
            new = set()
            for signature in parity:
                for side in allowed:
                    updated = list(signature)
                    updated[2 * color + side] |= mask
                    key = tuple(updated)
                    if key in new:
                        new.remove(key)
                    else:
                        new.add(key)
            parity = new
            if not parity:
                return set()
    return parity


def partition_moment_family(n, edges, layout, color_count, degree, *,
                            moduli=(), charges=None, pins=None, anchors=None):
    """Return score -> actual indexed colorings spanning degree-D moments.

    Sites and colors are zero-based. A layout is a site or a pair of layouts.
    A score has one tuple per color and one entry per cyclic group modulus.
    Optional anchors[i] is pinned to color i. Otherwise all nonempty connected
    partitions are covered. Loops and parallel edges use ordinary adjacency.
    """
    if n <= 0 or color_count <= 0 or degree < 0:
        raise ValueError("Use positive site/color counts and nonnegative degree")
    nodes = _layout_nodes(layout, n)
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError("Edge endpoint is out of range")
        if u != v:
            neighbors[u].add(v)
            neighbors[v].add(u)
    moduli = tuple(moduli)
    if any(m <= 0 for m in moduli):
        raise ValueError("Each modulus must be positive")
    if charges is None:
        charges = [(0,) * len(moduli) for _ in range(n)]
    if len(charges) != n or any(len(row) != len(moduli) for row in charges):
        raise ValueError("Supply one charge row per site and entry per modulus")
    pins = dict(pins or {})
    if any(not (0 <= v < n and 0 <= c < color_count) for v, c in pins.items()):
        raise ValueError("A prescribed site or color is out of range")
    if anchors is None:
        roots_to_try = permutations(range(n), color_count)
    else:
        roots = tuple(anchors)
        if (len(roots) != color_count or len(set(roots)) != color_count
                or any(not 0 <= v < n for v in roots)):
            raise ValueError("Choose one distinct physical anchor per color")
        roots_to_try = (roots,)

    def score(assignment):
        sums = [[0] * len(moduli) for _ in range(color_count)]
        for v, c in assignment.items():
            for j, m in enumerate(moduli):
                sums[c][j] = (sums[c][j] + charges[v][j]) % m
        return tuple(map(tuple, sums))

    def retained(fixed, roots):
        live = {}
        for index, (site, left, right) in enumerate(nodes):
            if site is not None:
                colors = (fixed[site],) if site in fixed else range(color_count)
                candidates = ({site: c} for c in colors)
            else:
                left_rows = live.pop(left)
                right_rows = live.pop(right)
                candidates = (a | b for a, b in product(left_rows, right_rows))
            answer = []
            bases = {}
            for assignment in candidates:
                signatures = _connectivity_features(assignment, neighbors, color_count, roots)
                if not signatures:
                    continue
                moments = _monomials(assignment, degree)
                tensor = {(signature, term) for signature in signatures for term in moments}
                reduced_basis = bases.setdefault(score(assignment), {})
                if _add_independent(reduced_basis, tensor):
                    answer.append(assignment)
            live[index] = answer
        return live[len(nodes) - 1]

    witnesses = {}
    global_bases = {}
    for roots in roots_to_try:
        if any(v in pins and pins[v] != c for c, v in enumerate(roots)):
            continue
        fixed = pins | {v: c for c, v in enumerate(roots)}
        for assignment in retained(fixed, roots):
            key = score(assignment)
            basis = global_bases.setdefault(key, {})
            if _add_independent(basis, _monomials(assignment, degree)):
                witnesses.setdefault(key, []).append(tuple(assignment[v] for v in range(n)))
    return witnesses


def polynomial_witness(family, score, terms):
    """Return one coloring making the GF(2) sum of the given monomials one.

    Each term is a sequence of (site, color) pairs. An empty term denotes 1.
    The caller must choose a family of sufficiently high degree.
    """
    terms = [tuple(term) for term in terms]
    for coloring in family.get(score, ()):
        if sum(all(coloring[v] == c for v, c in term) for term in terms) % 2:
            return coloring
    return None
