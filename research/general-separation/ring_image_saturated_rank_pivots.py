"""Decision and source witnesses by saturation followed by rooted rank pivots."""
import cnf_binary_span_saturation
import cnf_miss_span
import source_remote_pivot_rank
from read_two_ring_image import recover


def _caps(discovery_cap, rank_cap, branch_cap):
    for cap in (discovery_cap, rank_cap, branch_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("caps must be nonnegative integers or None")


def _canonical(rows):
    cleaned = set()
    for row in rows:
        literals = frozenset(row)
        if not any(-i in literals for i in literals):
            cleaned.add(tuple(sorted(literals)))
    return tuple(sorted(cleaned))


def solve_source_sparse(arity, clauses, *, discovery_cap=None, rank_cap=None, branch_cap=None):
    _caps(discovery_cap, rank_cap, branch_cap)
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    original = tuple(tuple(row) for row in clauses)
    if any(type(x) is not int or not 1 <= abs(x) <= arity for row in original for x in row):
        raise ValueError("invalid signed literal")
    canonical = _canonical(original)
    if any(len(row) > 3 for row in canonical):
        wide = cnf_miss_span.solve(arity, original, max_terms=branch_cap)
        result = dict(status=wide["status"], route="wide_span",
                      metrics={"terms": wide["terms"], "rank": wide["rank"]})
        if result["status"] == "unknown":
            result.update(reason=wide["reason"], available=wide["available"], required=wide["required"])
        true_ids = wide.get("true_ids")
    else:
        sat = cnf_binary_span_saturation.project(arity, original)
        # Recompute remote pivot ownership on every surviving original row.
        # A row redundant for rank can still offer a different pivot candidate.
        strengthened = _canonical(canonical + tuple(sat.derived))
        answer = source_remote_pivot_rank.solve(arity, strengthened, discovery_cap=discovery_cap,
                                                rank_cap=rank_cap, branch_cap=branch_cap)
        status = {"SAT": "nonzero", "UNSAT": "zero", "UNKNOWN": "unknown"}[answer["status"]]
        result = dict(status=status, route="saturated_pivots", metrics=answer["metrics"],
                      pivots=answer["pivots"], rank_history=sat.ranks, derived=sat.derived)
        if status == "unknown":
            result["reason"] = answer["reason"]
        true_ids = answer["true_variables"]
    if result["status"] == "nonzero":
        ids = set(true_ids)
        if not all(any((abs(x) in ids) == (x > 0) for x in row) for row in original):
            raise AssertionError("invalid original source witness")
        result["true_ids"] = tuple(sorted(ids))
    return result


def decide(n, clauses, point, k, *, discovery_cap=None, rank_cap=None, branch_cap=None):
    _caps(discovery_cap, rank_cap, branch_cap)
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    arity, formula = source
    result = solve_source_sparse(arity, formula, discovery_cap=discovery_cap,
                                 rank_cap=rank_cap, branch_cap=branch_cap)
    if result["status"] == "nonzero":
        ids = set(result["true_ids"])
        result["assignment"] = tuple(int(i in ids) for i in range(1, arity+1))
    return result
