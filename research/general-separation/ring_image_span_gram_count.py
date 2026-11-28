"""Complete exact ordered-image counting by clause-miss span and planar demand Gram rank."""
import cnf_miss_span
import ring_image_gram_demands
from read_two_ring_image import recover


def count(n, clauses, point, k, *, max_terms=None, max_determinants=None):
    """Caps charge actual raw trials (including witness work) and actual determinants."""
    for limit in (max_terms, max_determinants):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError("caps must be nonnegative integers or None")
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    a, formula = source
    basis = cnf_miss_span.project(a, formula).clauses
    rank = len(basis)
    h = len({abs(lit) for row in basis for lit in row})
    raw_bound = 0 if not basis or any(not row for row in basis) else min(1 << h, (h+1) << rank)
    threshold = 1 << min(h, rank)
    limit = max_determinants
    if max_terms is None or raw_bound <= max_terms:
        limit = threshold if limit is None else min(limit, threshold)
    gram = ring_image_gram_demands.decide_source(a, formula, max_determinants=limit)
    if gram["status"] in ("zero", "nonzero"):
        result = dict(gram, backend="gram", terms=0)
    else:
        raw = cnf_miss_span.solve(a, formula, max_terms=max_terms)
        result = dict(raw, backend="span", gram_attempt=gram, determinants=gram["determinants"])
        if raw["status"] != "unknown":
            mantissa, free = raw["count"]
            result["count"] = mantissa << free
            if mantissa:
                ids = set(raw["true_ids"])
                result["assignment"] = tuple(int(i in ids) for i in range(1, a+1))
    result.update(raw_rank=rank, basis_variables=h, raw_term_bound=raw_bound)
    if result["status"] == "unknown":
        return result
    if result["count"]:
        bits = result["assignment"]
        if len(bits) != a or not all(any(bits[abs(i)-1] == (i > 0) for i in row)
                                     for row in formula):
            raise AssertionError("invalid original source witness")
    modulus = 3 ** k
    result["value"] = pow(-15, k-a-1, modulus) * result["count"] % modulus
    return result


decide = count
