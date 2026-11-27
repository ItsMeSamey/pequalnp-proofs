"""Decision and original witnesses for the exact ordered selector-free ring image.

solve calls the ordered-image recognizer before applying sweep. The sweep uses
positive/negative one-based integer literals, in increasing variable order.
A bounded run stores at most twice the preceding frontier in provisional
states and applies its cap only AFTER normalization/dominance at each layer.
For a cap W all processing is polynomial in W and the explicit input size;
a refusal reports the measured width of that layer, not a minimum over orders.
An unrestricted run can use exponential space and time. Dominance allows
discarding solutions and must not be used as a count-preserving reduction.
"""
from read_two_ring_image import recover


def normalize(clauses):
    """Canonical clause antichain. None means an explicit empty clause."""
    unique = set()
    for row in clauses:
        clause = frozenset(row)
        if not clause:
            return None
        if not any(-i in clause for i in clause):
            unique.add(clause)
    return frozenset(c for c in unique if not any(d < c for d in unique))


def subsumption_implies(stronger, weaker):
    """Sound syntactic implication on normalized formulas; None denotes false."""
    if stronger is None:
        return True
    if weaker is None:
        return False
    return all(any(d <= c for d in stronger) for c in weaker)


def _restrict(formula, true_literal):
    return normalize(c - {-true_literal} for c in formula if true_literal not in c)


def sweep(arity, signed_clauses, *, max_states=None):
    """Return zero/nonzero/unknown. A witness uses original variable order."""
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise ValueError("invalid state budget")
    source = tuple(tuple(row) for row in signed_clauses)
    if any(type(i) is not int or not 1 <= abs(i) <= arity for row in source for i in row):
        raise ValueError("invalid signed literal")
    initial = normalize(source)
    states = {} if initial is None else {initial: 0}
    peak = 0
    for layer in range(arity+1):
        peak = max(peak, len(states))
        if max_states is not None and len(states) > max_states:
            return dict(status="unknown", reason="state_budget", layer=layer,
                        available=max_states, required=len(states), peak=peak)
        if not states:
            return dict(status="zero", peak=peak)
        if layer == arity:
            mask = states[frozenset()]
            assignment = tuple((mask >> i) & 1 for i in range(arity))
            if not all(any(assignment[abs(i)-1] == int(i > 0) for i in row)
                       for row in source):
                raise AssertionError("frontier returned an invalid source witness")
            return dict(status="nonzero", assignment=assignment, peak=peak)

        candidates = {}
        for formula, mask in states.items():
            for bit in (0, 1):
                literal = (layer+1) if bit else -(layer+1)
                residual = _restrict(formula, literal)
                if residual is not None:
                    candidates.setdefault(residual, mask | (bit << layer))
        # Distinct clause antichains cannot imply each other in both directions
        # by this test: mutual inclusion witnesses force every minimal clause
        # to be identical. Thus simultaneous pruning keeps all maximal states.
        states = {f: mask for f, mask in candidates.items()
                  if not any(f != g and subsumption_implies(f, g) for g in candidates)}
    raise AssertionError("missing terminal layer")


def solve(n, clauses, point, k, *, max_states=None):
    """Recognize the original four raw fields; attachments are never trusted."""
    recovered = recover(n, clauses, point, k)
    if recovered is None:
        return dict(status="off_image")
    arity, formula = recovered
    return sweep(arity, formula, max_states=max_states)
