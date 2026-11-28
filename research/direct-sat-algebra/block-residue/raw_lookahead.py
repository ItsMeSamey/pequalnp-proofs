"""One-raw-bit cofactor budget comparison on original NAND wiring."""

from corridor_nand import _net, _replay, _rows
from distinct_cones import cone_groups
from pair_optimizer import _Costs
from signed_cone_nand import _materialize, _translated, normalize, solve as signed_solve


def _score(inputs, gates, rows):
    """Reproduce signed normalization and projection without solving a chart."""
    retained, aliases = normalize(inputs, gates)
    groups = cone_groups(inputs, tuple((u[0], v[0]) for u, v in retained))
    if groups is None:
        raise AssertionError("signed normalization left tied operands")
    physical, expanded, blocks = _materialize(inputs, retained, groups)
    translated = _translated(rows, aliases)
    observed = {expanded[abs(l)-1] for row in translated for l in row}
    costs = _Costs(inputs, physical, observed)
    scores = [costs.score(block) for block in blocks]
    if None in scores:
        raise AssertionError("materialized block has too many entrances")
    return sum(scores)


def _cofactor(inputs, gates, rows, bit, value):
    # NAND(t,NAND(t,t)) is one. All three prefix gates normalize away.
    neg, one, zero = inputs, inputs+1, inputs+2
    prefix = ((bit, bit), (bit, neg), (one, one))
    constant = one if value else zero

    def image(w):
        if w == bit:
            return constant
        return w if w < inputs else w + len(prefix)

    rewritten = prefix + tuple((image(a), image(b)) for a, b in gates)
    mapped = tuple(tuple((image(abs(l)-1)+1) * (1 if l > 0 else -1) for l in row)
                   for row in rows)
    return rewritten, mapped


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None):
    """Return status, baseline b, split input or None, selected bs, original raw.

    Charge the sum of both branch budgets regardless of SAT/UNSAT outcomes.
    Ties keep the unsplit option, then the lowest physical input ID.
    """
    gates = _net(inputs, gates)
    n = inputs + len(gates)
    if output is not None:
        if type(output) is not int or not 0 <= output < n:
            raise ValueError("invalid designated output")
        pins = tuple(pins) + ((output, 1),)
    rows = tuple(_rows(n, clauses, pins, equalities))
    baseline = _score(inputs, gates, rows)
    budget = 1 << baseline
    selected = None
    scores = (baseline,)
    appearing = {w for gate in gates for w in gate if w < inputs}
    appearing.update(abs(l)-1 for row in rows for l in row if abs(l)-1 < inputs)
    for bit in sorted(appearing):
        bs = tuple(_score(inputs, *_cofactor(inputs, gates, rows, bit, value))
                   for value in (0, 1))
        candidate = (1 << bs[0]) + (1 << bs[1])
        if candidate < budget:
            budget = candidate
            selected, scores = bit, bs

    for value, expected in enumerate(scores):
        current, exterior = (gates, rows) if selected is None else _cofactor(
            inputs, gates, rows, selected, value)
        status, actual, _, raw = signed_solve(inputs, current, clauses=exterior)
        if actual != expected or status not in ("sat", "unsat"):
            raise AssertionError("selected solver disagreed with chart analysis")
        if status == "sat":
            lifted = list(raw)
            if selected is not None:
                lifted[selected] = value
            wires = _replay(lifted, gates)
            if any(not any(wires[abs(l)-1] == (l > 0) for l in row) for row in rows):
                raise AssertionError("cofactor witness failed original physical replay")
            return status, baseline, selected, scores, tuple(lifted)
    return "unsat", baseline, selected, scores, None
