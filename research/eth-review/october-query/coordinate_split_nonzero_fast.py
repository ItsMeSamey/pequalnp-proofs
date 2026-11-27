"""Physical empty-prefix shortcut for the frozen nonzero-cap adapter."""
from operator import index

from coordinate_split_nonzero_scores import recover_nonzero_prefix


def recover_nonzero(m, length, cap, score, *, max_calls, base=None):
    """Same score ABI and status schema, with immediate physical zero detection."""
    m, length, cap, max_calls = map(index, (m, length, cap, max_calls))
    if min(m, length, cap, max_calls) < 0:
        raise ValueError("negative parameter")
    paid = 0
    if base is None:
        if not max_calls:
            return dict(status="query_cap", calls=0, cache_hits=0, max_row_weight=0)
        base = score(((0, 0),)*length if m else ())
        paid = 1
    base = index(base)
    if base < 0:
        raise ValueError("negative prefix count")
    if not base:
        return dict(status="exact", histogram={}, count=0, calls=paid,
                    cache_hits=0, max_row_weight=0)
    result = recover_nonzero_prefix(m, length, cap, score, base=base,
                                    max_calls=max_calls-paid)
    result["calls"] += paid
    return result
