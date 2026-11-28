"""Complete exact model count and physical residue on the ordered selector-free image."""
from read_two_ring_image import recover
from ring_image_affine_demands import decide_source


def _cap(value):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError("caps must be nonnegative integers or None")


def count(n, clauses, point, k, *, max_assignments=None, max_determinants=None):
    """Both search resources are uncapped by default. Caps are independent."""
    _cap(max_assignments)
    _cap(max_determinants)
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    arity, formula = source
    live_rows = [row for row in formula if not any(-x in row for x in row)]
    labels = sorted({abs(x) for row in live_rows for x in row})
    d = len(labels)
    affordable = max_assignments is None or max_assignments.bit_length() > d
    determinant_cap = max_determinants
    if affordable and (determinant_cap is None or determinant_cap.bit_length() > d):
        determinant_cap = 1 << d
    result = decide_source(arity, formula, max_determinants=determinant_cap)
    if result["status"] in ("zero", "nonzero"):
        result = dict(result, backend="planar", assignments=0)
    elif not affordable:
        return dict(status="unknown", reason="assignment_budget", available=max_assignments,
                    required_log2=d, assignments=0, planar_attempt=result)
    else:
        index = {v: j for j, v in enumerate(labels)}
        masks = []
        for row in live_rows:
            literals = set(row)
            pos = sum(1 << index[x] for x in literals if x > 0)
            neg = sum(1 << index[-x] for x in literals if x < 0)
            masks.append((pos, neg))
        first = None
        total = 0
        trials = 1 << d
        for word in range(trials):
            if all((word & pos) or (~word & neg) for pos, neg in masks):
                total += 1
                if first is None:
                    first = word
        result = dict(status="nonzero" if total else "zero", count=total << (arity-d),
                      backend="source", determinants=result["determinants"],
                      planar_reason=result["reason"], assignments=trials)
        if first is not None:
            bits = [0] * arity
            for j, v in enumerate(labels):
                bits[v-1] = (first >> j) & 1
            result["assignment"] = tuple(bits)
    if result["count"]:
        bits = result["assignment"]
        if len(bits) != arity or not all(any(bits[abs(x)-1] == (x > 0) for x in row)
                                        for row in formula):
            raise AssertionError("invalid recovered source witness")
    modulus = 3 ** k
    result["value"] = pow(-15, k-arity-1, modulus) * result["count"] % modulus
    return result


decide = count
