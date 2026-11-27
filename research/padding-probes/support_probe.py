"""Find physical prediction disagreements using a Hamming ball about key zero."""

from itertools import combinations


def probe_support(m, d, construct, predict, *, baseline=None, query_cap=None):
    """Query integer keys of weight at most d, by weight and then bit positions.

    A nonzero multilinear polynomial on the Boolean cube of degree at most d
    cannot vanish on this ball: its coefficient for S is a signed sum of the
    values on subsets of S. If its support lies inside the disagreement region
    relative to f(0), the uncapped scan must therefore find a disagreement.

    The callbacks must be deterministic and construct must return stable
    physical formulas. A supplied baseline is an expected prediction at zero;
    that physical point is still queried and checked. query_cap includes this
    first query. calls counts predictions. input_bytes counts bytes submitted
    for bytes-valued formulas only. work tracks both callbacks.
    """
    if type(m) is not int or m < 0 or type(d) is not int or d < 0:
        raise ValueError("m and d must be nonnegative integers")
    if query_cap is not None and (type(query_cap) is not int or query_cap < 0):
        raise ValueError("query_cap must be a nonnegative integer or None")
    if not callable(construct) or not callable(predict):
        raise TypeError("construct and predict must be callable")

    work = {"construct_calls": 0, "predict_calls": 0}
    result = {"status": "unknown", "calls": 0, "work": work, "m": m,
              "degree_bound": d, "input_bytes": 0}

    def evaluate(key):
        formula = construct(key)
        work["construct_calls"] += 1
        if isinstance(formula, bytes):
            result["input_bytes"] += len(formula)
        prediction = predict(formula)
        work["predict_calls"] += 1
        result["calls"] = work["predict_calls"]
        return formula, prediction

    if query_cap == 0:
        return result
    reference, first = evaluate(0)
    if baseline is not None and baseline != first:
        raise ValueError("the supplied baseline differs from the physical prediction at zero")
    for weight in range(1, min(m, d) + 1):
        if result["calls"] == query_cap:
            return result
        for positions in combinations(range(m), weight):
            if result["calls"] == query_cap:
                return result
            key = sum(1 << j for j in positions)
            formula, prediction = evaluate(key)
            if prediction != first:
                if formula is reference or formula == reference:
                    raise ValueError("the same physical formula produced different predictions")
                result.update(status="disagreement", keys=(0, key),
                              formulas=(reference, formula), predictions=(first, prediction))
                return result

    if d >= m:
        result["status"] = "constant"
    return result
