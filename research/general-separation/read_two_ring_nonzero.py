"""Compile a signed CNF to a positive read-twice modular nonzero instance.

Source literals use signed one-based variable numbers. Output clauses and
metadata index the physical point from zero. The four fields n, clauses,
point, k are the arguments to positive_read_two_prime_power.evaluate.
The frontend performs only compilation. For every satisfying assignment
multiply its true-variable selectors (default +1), then sum to obtain Z.
The compiled value is (-15)**expanded_edges * Z modulo 3**k.
"""
import json
import sys

from read_two_prime_frontend import compile_cnf


def compile_nonzero(n, clauses, *, selectors=None):
    selectors = {} if selectors is None else dict(selectors)
    if any(type(x) is not int or x not in (-1, 0, 1) for x in selectors.values()):
        raise ValueError("selectors must be integers -1, 0, or 1")
    raw = compile_cnf(n, clauses, prime=None, t=4, selectors=selectors)
    exponent = raw["expanded_edges"]
    k = exponent + n + 1
    modulus = 3 ** k
    normalization = raw["normalization_variable"] - 1
    point = []
    for i, weight in enumerate(raw["weights"]):
        if i == normalization:
            point.append(1)
        else:
            inverse = pow(weight.denominator, -1, modulus)
            point.append(weight.numerator * inverse % modulus)
    return dict(n=len(point), clauses=tuple(tuple(i - 1 for i in clause)
                                            for clause in raw["clauses"]),
                point=tuple(point), k=k, expanded_edges=exponent,
                normalization_index=normalization,
                selector_indices={j: i - 1 for j, i in raw["selector_variables"].items()})


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    try:
        data = json.load(sys.stdin)
        if not isinstance(data, dict) or not {"n", "clauses"} <= data.keys() or (
                data.keys() - {"n", "clauses", "selectors"}):
            raise ValueError("expected n, clauses and optional selectors")
        raw_selectors = data.get("selectors", {})
        if not isinstance(raw_selectors, dict):
            raise ValueError("selectors must map source indices to signs")
        selectors = {int(j): x for j, x in raw_selectors.items()}
        if any(str(int(j)) != j for j in raw_selectors):
            raise ValueError("selector keys must be canonical decimal variable indices")
        result = compile_nonzero(data["n"], data["clauses"], selectors=selectors)
    except (ValueError, TypeError, KeyError) as exc:
        print(json.dumps(dict(status="error", reason=str(exc))))
        return 2
    print(json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
