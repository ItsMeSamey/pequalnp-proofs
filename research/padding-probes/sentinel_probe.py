"""Probe a SAT predictor on physically serialized, satisfiable strict 3-CNFs."""


def _dimacs(b):
    lines = [f"p cnf {3*b} {b}\n"]
    lines.extend(f"{i} {i+1} {i+2} 0\n" for i in range(1, 3*b+1, 3))
    return "".join(lines).encode("ascii")


def double_until_error(predict, *, max_clauses=None):
    """Probe b=1,2,4,... up to the inclusive cap; count all submitted bytes.

    With no cap the caller must promise eventual rejection on this sequence.
    On cap exhaustion, formula, witness and b describe the last submitted
    query, or None, None and 0 respectively if the cap admitted no query.
    A set bit i in witness assigns DIMACS variable i+1 true.
    """
    if not callable(predict):
        raise TypeError("predict must be callable")
    if max_clauses is not None and (type(max_clauses) is not int or max_clauses < 0):
        raise ValueError("max_clauses must be a nonnegative integer or None")
    result = dict(status="unknown", formula=None, witness=None, b=0, calls=0, input_bytes=0)
    b = 1
    while max_clauses is None or b <= max_clauses:
        formula = _dimacs(b)
        prediction = predict(formula)
        if type(prediction) not in (bool,int) or prediction not in (0,1):
            raise ValueError("predict must return a Boolean or integer 0 or 1")
        result.update(formula=formula, witness=(1 << (3*b))-1, b=b,
                      calls=result["calls"]+1, input_bytes=result["input_bytes"]+len(formula))
        if not prediction:
            result["status"] = "false_negative"
            break
        b *= 2
    return result


def sentinel_flat_predictor(R):
    """Return the exact codimension-R predictor on canonical sentinel bytes only.

    Each strict clause excludes one point in its triple and contains a
    codimension-one affine flat. Codimensions add on disjoint products.
    """
    if type(R) is not int or R < 0:
        raise ValueError("R must be a nonnegative integer")
    def predict(formula):
        if type(formula) is not bytes:
            raise ValueError("expected canonical sentinel DIMACS bytes")
        header, newline, body = formula.partition(b"\n")
        fields = header.split(b" ")
        if not newline or len(fields)!=4 or fields[:2]!=[b"p",b"cnf"] or not fields[3].isdigit():
            raise ValueError("invalid sentinel DIMACS header")
        b = int(fields[3])
        # Bound allocations by the physical input even on a forged huge header.
        if b < 1 or b > len(body)//8 or formula != _dimacs(b):
            raise ValueError("expected exactly the consecutive positive triples")
        return b <= R
    return predict
