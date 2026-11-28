"""Exact ordered-image counting with binary-background and span/Gram solvers."""
import cnf_binary_background_count
import ring_image_span_gram_count
from read_two_ring_image import recover


def _eligible(formula):
    for clause in formula:
        literals = set(clause)
        if len(literals) > 3 and all(-literal not in literals for literal in literals):
            return False
    return True


def count(n, clauses, point, k, *, max_round=None):
    """Limit each counter in each attempt to max_round. Report cumulative charges."""
    if max_round is not None and (type(max_round) is not int or max_round < 0):
        raise ValueError("max_round must be a nonnegative integer or None")
    source = recover(n, clauses, point, k)
    if source is None:
        return {"status": "off_image"}
    arity, formula = source
    eligible = _eligible(formula)
    charges = {"background_terms": 0, "span_terms": 0, "determinants": 0}
    quota = min(1, max_round) if max_round is not None else 1
    rounds = 0
    while True:
        rounds += 1
        if eligible:
            result = cnf_binary_background_count.count(arity, formula, max_terms=quota)
            charges["background_terms"] += result["terms"]
            if result["status"] in ("nonzero", "zero"):
                mantissa, free = result["count"]
                total = mantissa << free
                answer = dict(result, backend="binary_background", count=total)
                if total:
                    ids = set(result["true_ids"])
                    bits = tuple(int(i in ids) for i in range(1, arity + 1))
                    if not all(any(bits[abs(lit) - 1] == (lit > 0) for lit in row)
                               for row in formula):
                        raise AssertionError("invalid recovered source witness")
                    answer["assignment"] = bits
                modulus = 3 ** k
                answer["value"] = pow(-15, k - arity - 1, modulus) * total % modulus
                return dict(answer, rounds=rounds, last_quota=quota, charges=charges)

        result = ring_image_span_gram_count.count(
            n, clauses, point, k, max_terms=quota, max_determinants=quota
        )
        charges["span_terms"] += result["terms"]
        charges["determinants"] += result["determinants"]
        if result["status"] in ("nonzero", "zero"):
            return dict(result, rounds=rounds, last_quota=quota, charges=charges)
        if result["status"] != "unknown":
            raise AssertionError("ordered-image decoders disagree")
        if quota == max_round:
            return dict(status="unknown", reason="round_limit", rounds=rounds,
                        last_quota=quota, charges=charges)
        quota *= 2
        if max_round is not None:
            quota = min(quota, max_round)
