"""Exact integer shell schedules for a complete dyadic valuation grid."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Schedule:
    multiplicities: tuple
    precisions: tuple
    slots: int
    cost: int | None = None


def populations(a, outer=False):
    """Full signed cardinal grid, or nonzero active valuations of outer representatives.

    Outer representatives support i<a-1 only; omitted top residues have zero
    multiplicity. Their SAME-shell denominator losses are still included.
    """
    if type(a) is not int or a < 1:
        raise ValueError("packet exponent must be positive")
    if outer:
        return tuple(1 << (a-1-i) for i in range(a-1))
    return tuple(1 << (a-i) for i in range(a+1))


def _setup(a, p, caps, degree, outer):
    pop = populations(a, outer)
    caps = tuple(caps)
    if len(caps) != len(pop) or type(p) is not int or p < 1:
        raise ValueError("invalid shell caps or origin precision")
    if type(degree) is not int or degree < 0:
        raise ValueError("degree must be nonnegative")
    if any(x is not None and (type(x) is not int or x < 0) for x in caps):
        raise ValueError("use nonnegative precision caps or None for forbidden shells")
    # Complete higher residue shells, including forced-inactive ones.
    top = a - 1 if outer else a
    losses = tuple(sum((h-i) * (1 << (top-h)) for h in range(i+1, top+1))
                   for i in range(len(pop)))
    return pop, caps, losses


def _limit(cap, p, k, loss, tail):
    if cap is None:
        return 0
    return max(0, (cap-p+k+tail) // (k+loss))


def _precision(q, p, k, loss, tail):
    return max(0, p + (q-1)*k + q*loss-tail) if q else 0


def greatest(a, p, caps, degree, *, outer=False):
    """Return greatest cap-feasible vector meeting the degree or None."""
    pop, caps, losses = _setup(a, p, caps, degree, outer)
    qs, ps = [0]*len(pop), [0]*len(pop)
    mass = moment = 0
    for i in reversed(range(len(pop))):
        k = a+1-i
        tail = moment-i*mass
        qs[i] = _limit(caps[i], p, k, losses[i], tail)
        ps[i] = _precision(qs[i], p, k, losses[i], tail)
        delta = pop[i]*qs[i]
        mass += delta
        moment += i*delta
    return Schedule(tuple(qs), tuple(ps), mass) if mass > degree else None


def minimum_cost(a, p, caps, degree, per_node, *, outer=False):
    """Minimize sum of population times integer per_node(i,q,precision).

    Inactive shells have zero charge. Cost function must include any desired
    acquisition/continuation charges and have no dependence on earlier state.
    """
    pop, caps, losses = _setup(a, p, caps, degree, outer)
    if greatest(a, p, caps, degree, outer=outer) is None:
        return None
    states = {(0, 0): 0}
    history = {}
    for i in reversed(range(len(pop))):
        following = {}
        back = {}
        k = a+1-i
        for (mass, moment), paid in states.items():
            tail = moment-i*mass
            limit = _limit(caps[i], p, k, losses[i], tail)
            for q in range(limit+1):
                precision = _precision(q, p, k, losses[i], tail)
                charge = per_node(i, q, precision) if q else 0
                if type(charge) is not int or charge < 0:
                    raise ValueError("per-node cost must be a nonnegative integer")
                delta = pop[i]*q
                state = (mass+delta, moment+i*delta)
                total = paid + pop[i]*charge
                if state not in following or total < following[state]:
                    following[state] = total
                    back[state] = ((mass, moment), q, precision)
        states = following
        history[i] = back
    end = min((state for state in states if state[0] > degree),
              key=states.__getitem__)
    slots, cost = end[0], states[end]
    qs, ps = [], []
    for i in range(len(pop)):
        end, q, precision = history[i][end]
        qs.append(q)
        ps.append(precision)
    return Schedule(tuple(qs), tuple(ps), slots, cost)
