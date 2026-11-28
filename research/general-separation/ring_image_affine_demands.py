"""Four-field ordered-image decisions via affine demand filters on actual matchings."""
from read_two_ring_image import recover
from ring_image_clique_matching import _root
from planar_character_oracle import CharacterOracle, DeterminantBudget
from pm_demand_affine import classify


def _cap(cap):
    if cap is not None and (type(cap) is not int or cap < 0):
        raise ValueError("invalid determinant budget")


def _filters(left, right, pairs, ids, demands):
    reference = classify(left, right, pairs, ())
    if reference["status"] == "empty":
        return None
    base, directions = reference["base"], reference["directions"]
    position = {x:i for i,x in enumerate(ids)}
    pivots, checks, nonlinear = {}, [], []
    affine_count = 0
    inconsistent = False
    for demand in demands:
        result = classify(left,right,pairs,[position[x] for x in sorted(demand)])
        if result["status"] == "nonaffine":
            nonlinear.append(demand)
            continue
        if result["status"] != "affine":
            raise AssertionError("nonempty matching base changed")
        affine_count += 1
        mask, rhs = result["mask"], 1 ^ result["constant"]
        row = sum(((mask & v).bit_count() % 2) << j for j,v in enumerate(directions))
        bit = rhs ^ ((mask & base).bit_count() % 2)
        while row:
            pivot = row.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = row, bit
                checks.append((mask,rhs))
                break
            prior, parity = pivots[pivot]
            row, bit = row ^ prior, bit ^ parity
        else:
            if bit:
                inconsistent = True
    stats = dict(affine_count=affine_count,affine_rank=len(checks),nonaffine_count=len(nonlinear))
    return checks, nonlinear, inconsistent, stats


def _filtered(oracle, ids, checks, nonlinear, removed):
    numerator = 0
    for subset in range(1 << len(checks)):
        character = phase = 0
        for i,(mask,rhs) in enumerate(checks):
            if subset & (1 << i):
                character ^= mask
                phase ^= rhs
        negative = tuple(x for j,x in enumerate(ids) if character & (1 << j))
        for miss in range(1 << len(nonlinear)):
            deleted = set(removed)
            for i,demand in enumerate(nonlinear):
                if miss & (1 << i):
                    deleted.update(demand)
            term = oracle.count(negative=negative, deleted=deleted)
            numerator += -term if phase ^ (miss.bit_count() % 2) else term
    total, remainder = divmod(numerator, 1 << len(checks))
    if remainder or total < 0:
        raise AssertionError("invalid signed matching count")
    return total


def decide_source(arity, signed_clauses, *, max_determinants=None):
    """One-based signed source. Workspace is polynomial in the declared arity."""
    import networkx as nx
    _cap(max_determinants)
    formula = tuple(tuple(row) for row in signed_clauses)
    if type(arity) is not int or arity < 0 or any(
            type(x) is not int or not 1 <= abs(x) <= arity for row in formula for x in row):
        raise ValueError("invalid signed source")
    conflict = nx.Graph()
    conflict.add_nodes_from(range(1,arity+1))
    demands = set()
    for raw in formula:
        row = frozenset(raw)
        if all(x > 0 for x in row):
            demands.add(row)
        elif len(row) == 2 and all(x < 0 for x in row):
            conflict.add_edge(*sorted(-x for x in row))
        else:
            return dict(status="unknown", reason="clause_syntax", determinants=0)
    reconstructed = _root(nx,conflict)
    if reconstructed is None:
        return dict(status="unknown", reason="line_graph", determinants=0)
    root, edges = reconstructed
    stars = {v:frozenset(root[v][w]["variable"] for w in root[v]) for v in root}
    if not set(stars.values()) <= demands:
        return dict(status="unknown", reason="missing_star", determinants=0)
    if not nx.is_bipartite(root):
        return dict(status="unknown", reason="nonbipartite", determinants=0)
    if not nx.check_planarity(root)[0]:
        return dict(status="unknown", reason="nonplanar", determinants=0)
    zero = dict(status="zero",count=0,determinants=0)
    if frozenset() in demands:
        return zero
    if not edges:
        return dict(status="nonzero",count=1,assignment=(),determinants=0,
                    affine_rank=0,affine_count=0,nonaffine_count=0)
    blocked, extras = set(), []
    for row in demands:
        centers = set.intersection(*(set(edges[x]) for x in row))
        if centers:
            for v in centers:
                blocked.update(stars[v]-row)
        else:
            extras.append(row)
    ids = sorted(set(edges)-blocked)
    restricted = {frozenset(row-blocked) for row in extras}
    if frozenset() in restricted:
        return zero
    demands = sorted((row for row in restricted if not any(other < row for other in restricted)),
                     key=lambda r:tuple(sorted(r)))
    color = nx.bipartite.color(root)
    left = {v:i for i,v in enumerate(sorted(v for v in root if color[v]))}
    right = {v:i for i,v in enumerate(sorted(v for v in root if not color[v]))}
    pairs = []
    for x in ids:
        u,v = edges[x]
        if u not in left:
            u,v = v,u
        pairs.append((left[u],right[v]))
    filters = _filters(len(left),len(right),pairs,ids,demands)
    if filters is None:
        return zero
    checks, nonlinear, inconsistent, stats = filters
    if inconsistent:
        return dict(**zero, **stats)
    oracle = CharacterOracle(root,max_determinants=max_determinants)
    try:
        removed = set(blocked)
        total = _filtered(oracle,ids,checks,nonlinear,removed)
        if not total:
            return dict(status="zero",count=0,determinants=oracle.calls,**stats)
        for x in ids:
            if _filtered(oracle,ids,checks,nonlinear,removed | {x}):
                removed.add(x)
    except DeterminantBudget as exc:
        return dict(status="unknown", reason="determinant_budget", available=exc.available,
                    required=exc.required, determinants=oracle.calls, **stats)
    assignment = tuple(int(x not in removed) for x in range(1,arity+1))
    if not all(any(assignment[abs(x)-1] == (x>0) for x in row) for row in formula):
        raise AssertionError("invalid original matching witness")
    return dict(status="nonzero",count=total,assignment=assignment,determinants=oracle.calls,**stats)


def decide(n, clauses, point, k, *, max_determinants=None):
    _cap(max_determinants)
    source = recover(n,clauses,point,k)
    if source is None:
        return dict(status="off_image")
    arity,formula = source
    result = decide_source(arity,formula,max_determinants=max_determinants)
    if result["status"] in ("nonzero","zero"):
        modulus = 3 ** k
        result["value"] = pow(-15,k-arity-1,modulus)*result["count"] % modulus
    return result


solve = decide
