"""Trace-family probes for a Walsh-sparse response on integer padding keys."""


def _mod(value, modulus):
    while value and value.bit_length() >= modulus.bit_length():
        value ^= modulus << (value.bit_length() - modulus.bit_length())
    return value


def _mul(left, right, modulus, size):
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
        if left & size:
            left ^= modulus
    return product


def _irreducible(modulus, degree):
    size = 1 << degree
    x = _mod(2, modulus)
    power = x
    for j in range(1, degree + 1):
        power = _mul(power, power, modulus, size)
        if j <= degree // 2:
            a, b = modulus, power ^ x
            while b:
                a, b = b, _mod(a, b)
            if a != 1:
                return False
    return power == x


def probe(m, s, construct, predict, *, promised=False):
    """Find two actual formulas with differing deterministic scalar predictions.

    construct(key) takes an integer mask, bit j = Tr(beta*alpha**j), and must
    return a stable formula. predict(formula) supplies the response. Promised
    sparsity bounds the number of nonzero Walsh modes over a field of odd or
    zero characteristic. Each distinct queried key incurs one call per callback.
    The modulus and field elements use bit i for the coefficient of X**i.
    Exhaustion takes O(q² m) field multiplications after construction and stores
    at most q² keys. Scanning O(q) modulus candidates costs poly(log q) per
    candidate. Calls counts predictions; work gives both callback counts.
    physical_input_bytes totals the lengths of all byte formulas sent to predict;
    it is None if any queried formula is not bytes.
    """
    if type(m) is not int or type(s) is not int or m < 0 or s < 0:
        raise ValueError("m and s must be nonnegative integers")
    work = dict(construct_calls=0, predict_calls=0, pairs_examined=0)
    result = dict(status="constant" if promised or m == 0 else "unknown", calls=0,
                  physical_input_bytes=0,
                  m=m, sparsity_bound=s, work=work, field=None)
    if m == 0:
        return result
    degree = max(1, (s * (m - 1)).bit_length())
    size = 1 << degree
    modulus = next(p for p in range(size | 1, 2 * size, 2) if _irreducible(p, degree))
    result["field"] = dict(degree=degree, size=size, modulus=modulus,
                           modulus_candidates=(modulus-size+1)//2, pair_bound=size*size)
    trace_mask = 0
    for j in range(degree):
        trace, power = 0, 1 << j
        for _ in range(degree):
            trace ^= power
            power = _mul(power, power, modulus, size)
        if trace not in (0, 1):
            raise ArithmeticError("field trace is outside GF(2)")
        trace_mask |= trace << j

    def evaluate(key):
        formula = construct(key)
        work["construct_calls"] += 1
        if not isinstance(formula, bytes):
            result["physical_input_bytes"] = None
        elif result["physical_input_bytes"] is not None:
            result["physical_input_bytes"] += len(formula)
        prediction = predict(formula)
        work["predict_calls"] += 1
        result["calls"] = work["predict_calls"]
        return formula, prediction

    reference, baseline = evaluate(0)
    seen = {0}
    for alpha in range(size):
        for beta in range(size):
            work["pairs_examined"] += 1
            term, key = beta, 0
            for j in range(m):
                key |= ((term & trace_mask).bit_count() % 2) << j
                term = _mul(term, alpha, modulus, size)
            if key in seen:
                continue
            seen.add(key)
            formula, prediction = evaluate(key)
            if prediction != baseline:
                if formula is reference or (isinstance(formula, bytes) and
                                            isinstance(reference, bytes) and formula == reference):
                    raise ValueError("one formula produced two different predictions")
                result.update(status="disagreement", keys=(0, key),
                              formulas=(reference, formula), predictions=(baseline, prediction))
                return result
    return result
