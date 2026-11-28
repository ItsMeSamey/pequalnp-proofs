"""Positive rational Gram compression of exact ordered-image matching demands.

For u residual nonlinear demands, rank rho, r affine checks and e allowed
edges the number of oracle requests is bounded by u(u+1)/2+(1+e)2**(r+rho).
One oracle tracks actual determinants, including global sign calibration.
The O(u**3) reduced rational Schur operations have polynomial bit cost:
entries are ratios of bordered/principal minors, of bit length
O(u*(e+log(u+2))) by Hadamard since every count is at most 2**e.
"""
from fractions import Fraction
from read_two_ring_image import recover
from ring_image_clique_matching import _root
from ring_image_affine_demands import _cap, _filters, _filtered
from planar_character_oracle import CharacterOracle, DeterminantBudget


def _prepare(arity, signed_clauses):
    """One-based signed source. Workspace is polynomial in the declared arity."""
    import networkx as nx
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
                    affine_rank=0,affine_count=0,nonaffine_count=0,gram_rank=0,gram_determinants=0)
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
    return root,formula,ids,blocked,checks,nonlinear,stats


def _gram_basis(oracle, blocked, demands):
    """Indices of independent miss indicators on the entire allowed PM family."""
    u = len(demands)
    matrix = [[Fraction(0) for _ in demands] for _ in demands]
    cache = {}
    for i, first in enumerate(demands):
        for j in range(i,u):
            deleted = frozenset(blocked | first | demands[j])
            if deleted not in cache:
                cache[deleted] = oracle.count(deleted=deleted)
            matrix[i][j] = matrix[j][i] = Fraction(cache[deleted])
    selected = []
    for i in range(u):
        pivot = matrix[i][i]
        if not pivot:
            # A zero diagonal of the residual Gram matrix means a zero vector.
            continue
        if pivot < 0:
            raise AssertionError("negative Gram pivot")
        selected.append(i)
        for j in range(i+1,u):
            multiplier = matrix[i][j]/pivot
            for k in range(j,u):
                matrix[j][k] -= multiplier*matrix[i][k]
                matrix[k][j] = matrix[j][k]
    return selected


def decide_source(arity, signed_clauses, *, max_determinants=None):
    _cap(max_determinants)
    prepared = _prepare(arity,signed_clauses)
    if isinstance(prepared,dict):
        return prepared
    root,formula,ids,blocked,checks,nonlinear,stats = prepared
    oracle = CharacterOracle(root,max_determinants=max_determinants)
    gram_complete = False
    try:
        indices = _gram_basis(oracle,blocked,nonlinear)
        stats.update(gram_rank=len(indices),gram_determinants=oracle.calls)
        gram_complete = True
        basis = [nonlinear[i] for i in indices]
        removed = set(blocked)
        total = _filtered(oracle,ids,checks,basis,removed)
        if not total:
            return dict(status="zero",count=0,determinants=oracle.calls,**stats)
        for x in ids:
            if _filtered(oracle,ids,checks,basis,removed | {x}):
                removed.add(x)
    except DeterminantBudget as exc:
        if not gram_complete:
            stats["gram_determinants"] = oracle.calls
        return dict(status="unknown",reason="determinant_budget",available=exc.available,
                    required=exc.required,determinants=oracle.calls,**stats)
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
