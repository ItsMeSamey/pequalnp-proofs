"""Sharp nonzero-word-cap variant of the frozen fixed-prefix score adapter."""
from operator import index

from coordinate_split_scores import recover_prefix


def recover_nonzero_prefix(m, length, cap, score, *, max_calls, base=None):
    """cap counts distinct NONZERO accepted words. Query metrics are original calls."""
    cap = index(cap)
    if cap < 0:
        raise ValueError("negative nonzero support cap")

    # A single extra atom at zero survives every homogeneous parity probe.
    # Thus the augmented total support is exactly 1 + original nonzero support,
    # at every coordinate prefix as well as after the last coordinate.
    def augmented_score(row):
        value = index(score(row))
        if value < 0:
            raise ValueError("negative physical score")
        return value + 1

    if base is not None:
        base = index(base)
        if base < 0:
            raise ValueError("negative prefix count")
        base += 1
    result = recover_prefix(m, length, cap + 1, augmented_score,
                            max_calls=max_calls, base=base)
    if result["status"] == "support_overflow":
        result["certified_at_least"] -= 1
    elif result["status"] == "exact":
        histogram = result["histogram"]
        histogram[0] -= 1
        if not histogram[0]:
            del histogram[0]
        result["count"] = histogram.get(0, 0)
    return result
