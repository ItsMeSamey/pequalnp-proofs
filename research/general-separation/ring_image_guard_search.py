"""Complete selector-free image decision with a preflight exponential-search cap."""
from read_two_ring_image import recover
from ring_image_two_boundary_phases import decide as phase_decide


def decide(n, clauses, point, k, *, max_assignments=4096):
    """None allows unbounded search. The cap reserves whole Boolean assignments."""
    if max_assignments is not None and (type(max_assignments) is not int or max_assignments < 0):
        raise ValueError("max_assignments must be a nonnegative integer or None")
    result = phase_decide(n, clauses, point, k)
    if result["status"] != "unknown":
        return dict(result, search="none", tested=0)

    if "projection" in result:
        projection = result["projection"]
        rows = projection.residual
        lift = projection.lift
        mode = "residual"
    else:
        # Chart recognition already established image membership. Reconstruct
        # the same source without relying on any planted gadget labels.
        arity, formula = recover(n, clauses, point, k)
        rows = [row for row in formula if not any(-lit in row for lit in row)]
        mode = "source"

        def lift(true_ids):
            bits = tuple(int(i in true_ids) for i in range(1, arity+1))
            if not all(any(bits[abs(i)-1] == (i > 0) for i in row) for row in formula):
                raise AssertionError("exhaustive assignment fails recovered source")
            return bits

    labels = sorted({abs(i) for row in rows for i in row})
    dimension = len(labels)
    # For C >= 0, C < 2**r iff C.bit_length() <= r. Report the
    # exponent on refusal without allocating a numeral of r+1 bits.
    if max_assignments is not None and max_assignments.bit_length() <= dimension:
        return dict(status="unknown", reason="assignment_budget", search=mode,
                    required_log2=dimension, available=max_assignments, tested=0)
    positions = {v: j for j, v in enumerate(labels)}
    masks = []
    for row in rows:
        pos = sum(1 << positions[v] for v in set(row) if v > 0)
        neg = sum(1 << positions[-v] for v in set(row) if v < 0)
        masks.append((pos, neg))
    required = 1 << dimension
    for word in range(required):
        if all((word & pos) or ((~word) & neg) for pos, neg in masks):
            true_ids = {v for v, j in positions.items() if word >> j & 1}
            return dict(status="nonzero", assignment=lift(true_ids),
                        search=mode, dimension=dimension, tested=word+1)
    return dict(status="zero", search=mode, dimension=dimension, tested=required)
