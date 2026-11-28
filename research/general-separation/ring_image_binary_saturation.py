"""Exact ordered-image counting by competition with a saturated binary background."""
import cnf_binary_background_count as background
import cnf_binary_span_saturation as saturation
import ring_image_binary_background as original
from read_two_ring_image import recover


def count(n, clauses, point, k, *, max_round=None):
    """max_round bounds each primitive quota per attempt, including nested attempts."""
    if max_round is not None and (type(max_round) is not int or max_round < 0):
        raise ValueError("max_round must be a nonnegative integer or None")
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    arity, formula = source
    if not original._eligible(formula):
        answer = original.count(n, clauses, point, k, max_round=max_round)
        return dict(answer, route="wide_delegate",
                    charges=dict(answer["charges"], saturated_terms=0))
    sat = saturation.project(arity, formula)
    strengthened = sat.original + sat.derived
    charges = dict(saturated_terms=0, background_terms=0, span_terms=0, determinants=0)
    quota = min(1, max_round) if max_round is not None else 1
    attempts = 0
    while True:
        attempts += 1
        meta = dict(attempts=attempts, last_quota=quota, charges=charges,
                    rank_history=sat.ranks, derived=sat.derived)
        child = background.count(arity, strengthened, max_terms=quota)
        charges["saturated_terms"] += child["terms"]
        if child["status"] in ("zero", "nonzero"):
            mantissa, free = child["count"]
            total = mantissa << free
            answer = dict(child, count=total, route="saturated", **meta)
            if total:
                ids = set(child["true_ids"])
                bits = tuple(int(i in ids) for i in range(1, arity+1))
                if not all(any(bits[abs(i)-1] == (i > 0) for i in row) for row in formula):
                    raise AssertionError("saturated model fails original source")
                answer["assignment"] = bits
            modulus = 3 ** k
            answer["value"] = pow(-15, k-arity-1, modulus) * total % modulus
            return answer
        candidate = original.count(n, clauses, point, k, max_round=quota)
        for key, amount in candidate["charges"].items():
            charges[key] += amount
        if candidate["status"] in ("zero", "nonzero"):
            return dict(candidate, route="original", **meta)
        if candidate["status"] != "unknown" or child["status"] != "unknown":
            raise AssertionError("unexpected competing status")
        if quota == max_round:
            return dict(status="unknown", reason="round_limit", **meta)
        quota *= 2
        if max_round is not None:
            quota = min(quota, max_round)


decide = count
