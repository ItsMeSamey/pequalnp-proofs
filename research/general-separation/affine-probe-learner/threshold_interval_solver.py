"""Exact SAT search using majority forecasts on the canonical prefix queries.

Input JSON is {"n": number_of_inputs, "F": [nand_gate_pairs, output_wire]}.
Inputs are MSB first. Constants -1 and -2 denote zero and one. The decision
search uses state_dependent_interval_repair and can take exponential time.
Set PYTHONINTMAXSTRDIGITS=0 for large decimal assignments in the CLI.
"""
import json
import sys

from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import endpoint, evaluate, public_cap
from state_dependent_interval_repair import solve as interval_repair


class UnsupportedQuery(ValueError):
    """The supplied NAND presentation is outside the prefix query language."""


def forecast_factory(n, F):
    """Return a deterministic callable (n, cap, history, query) -> bit.

    For N=2**n use virtual seeds (x,b), omitting (0,1-F(0)). At index j the
    virtual label is b AND [x<=j]. At the constant-zero sentinel the label
    is always zero, including when the two sentinel presentations coincide.
    The true pair (x,F(x)) survives all honest feedback. Conditioning on
    every observation only decreases the version space. With ties predicting
    zero, n+1 mistakes would leave at most floor((2*N-1)/2**(n+1))=0 pairs.
    Empty counterfactual histories default to zero after full validation.
    """
    _natural(n, "n")
    gates, output = _source(n, F)
    total = 1 << n
    anchor = evaluate(n, gates, output, 0)
    zero = endpoint(n, gates, output, -1)
    full = endpoint(n, gates, output, total - 1)

    def parse(query, cap):
        try:
            pairs, root = _source(n, query)
        except (TypeError, ValueError) as exc:
            raise UnsupportedQuery("invalid NAND circuit") from exc
        if len(pairs) > cap:
            raise UnsupportedQuery("query exceeds public NAND cap")
        current = pairs, root
        if current == zero:
            return -1
        if current == full:
            return total - 1
        if root < n:
            raise UnsupportedQuery("missing prefix conjunction")
        first, second = pairs[root - n]
        if first != second or first < n:
            raise UnsupportedQuery("missing outer NAND inversion")
        _, threshold = pairs[first - n]
        # Locate the last one of the purported threshold. Arbitrary functions
        # can fool the bisection, so regenerate and compare the entire circuit.
        lo, hi = -1, total
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if evaluate(n, pairs, threshold, mid):
                lo = mid
            else:
                hi = mid
        if not 0 <= lo < total - 1 or current != endpoint(n, gates, output, lo):
            raise UnsupportedQuery("not a canonical source prefix")
        return lo

    def forecast(arity, cap, history, query):
        _natural(arity, "arity")
        _natural(cap, "cap")
        if arity != n:
            raise ValueError("learner arity mismatch")
        low, high = 0, total - 1
        zeros = total - int(anchor == 1)
        for prior, label in history:
            if type(label) not in (bool, int) or label not in (0, 1):
                raise ValueError("invalid feedback bit")
            index = parse(prior, cap)
            if label:
                zeros = 0
                high = min(high, index)
            else:
                low = max(low, index + 1)

        def ones_through(index):
            end = min(index, high)
            return max(0, end - low + 1) - int(anchor == 0 and low == 0 and end >= 0)

        index = parse(query, cap)
        positive = ones_through(index)
        population = zeros + ones_through(total - 1)
        return int(2 * positive > population)

    return forecast


def solve(n, F):
    """Return a verified original assignment or exhaustive branch rejection."""
    _natural(n, "n")
    F = _source(n, F)
    cap = public_cap(n, len(F[0]))
    answer = interval_repair(n, F, cap, n, forecast_factory(n, F))
    return dict(**answer, bound=n, cap=cap)


def main():
    data = json.load(sys.stdin)
    print(json.dumps(solve(data["n"], data["F"]), separators=(",", ":")))


if __name__ == "__main__":
    main()
