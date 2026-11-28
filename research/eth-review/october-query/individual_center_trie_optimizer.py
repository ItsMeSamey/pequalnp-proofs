"""Exact separable Hermite acquisition on a dyadic center grid; numeric caps."""
from dataclasses import dataclass
from functools import lru_cache


@dataclass(frozen=True)
class CenterSchedule:
    # Each positive order gives (center, order, required bits, purchased bits).
    centers: tuple
    slots: int
    cost: int


def optimize(a, p, caps_by_t, degree, price):
    """Missing/None caps forbid centers. price(t,q,bits) is nonnegative integral.

    The assigned cost includes exactly the caller's charge for an active
    acquisition; price(t,q,0) may be zero when no data need to be queried.
    Numerical caps, search, and any price-oracle evaluations must be charged.
    """
    if type(a) is not int or a < 1 or type(p) is not int or p < 1:
        raise ValueError("invalid lattice or origin precision")
    if type(degree) is not int or degree < 0:
        raise ValueError("invalid degree")
    L = 1 << a
    allowed = {}
    for t, cap in caps_by_t.items():
        if type(t) is not int or t == 0 or not -L <= t < L:
            raise ValueError("invalid interpolation center")
        if cap is None:
            continue
        if type(cap) is not int or cap < 0:
            raise ValueError("invalid precision cap")
        allowed[t] = cap

    # Missing branches have zero mass. Keep all unary levels of retained paths.
    maxcap = {}
    leaves = {}
    for t, cap in sorted(allowed.items()):
        i = (abs(t) & -abs(t)).bit_length() - 1
        code = (t // (1 << i)) >> 1
        for depth in range(a-i+1):
            prefix = code % (1 << depth)
            node = (i, depth, prefix)
            maxcap[node] = max(maxcap.get(node, -1), cap)
        leaves[node] = t

    @lru_cache(None)
    def buy(t, q, required):
        best = None
        for bits in range(required, allowed[t]+1):
            cost = price(t, q, bits)
            if type(cost) is not int or cost < 0:
                raise ValueError("invalid acquisition cost")
            item = (cost, bits)
            if best is None or item < best:
                best = item
        return best

    @lru_cache(None)
    def subtree(i, depth, prefix, tail, mass, ancestors):
        if mass == 0:
            return (0, ())
        node = (i, depth, prefix)
        cap = maxcap.get(node)
        if cap is None:
            return None
        k = a+1-i
        # Every active leaf pays at least this partial ancestor/mass sum.
        if p-tail-k+ancestors+mass > cap:
            return None
        if depth == a-i:
            t = leaves[node]
            required = max(0, p-tail-k+mass+ancestors)
            cost, bits = buy(t, mass, required)
            return cost, ((t, mass, required, bits),)
        child_depth = depth+1
        right_prefix = prefix + (1 << depth)
        left_present = (i, child_depth, prefix) in maxcap
        right_present = (i, child_depth, right_prefix) in maxcap
        low = 0 if right_present else mass
        high = mass if left_present else 0
        best = None
        for left_mass in range(low, high+1):
            left = subtree(i, child_depth, prefix, tail, left_mass, ancestors+mass)
            if left is None:
                continue
            right = subtree(i, child_depth, right_prefix, tail, mass-left_mass, ancestors+mass)
            if right is None:
                continue
            proposal = (left[0]+right[0], left[1]+right[1])
            if best is None or proposal[0] < best[0]:
                best = proposal
        return best

    states = {(0, 0): (0, ())}
    for i in reversed(range(a+1)):
        root_cap = maxcap.get((i, 0, 0))
        if root_cap is None:
            continue
        next_states = {}
        for (higher_mass, higher_moment), (paid, witness) in states.items():
            tail = higher_moment-i*higher_mass
            limit = max(0, root_cap-p+(a+1-i)+tail)
            for mass in range(limit+1):
                choice = subtree(i, 0, 0, tail, mass, 0)
                if choice is None:
                    continue
                key = (higher_mass+mass, higher_moment+i*mass)
                cost = paid+choice[0]
                if key not in next_states or cost < next_states[key][0]:
                    next_states[key] = (cost, witness+choice[1])
        states = next_states
    best = None
    for (mass, moment), (cost, witness) in states.items():
        if mass > degree and (best is None or cost < best.cost):
            best = CenterSchedule(tuple(sorted(witness)), mass, cost)
    return best
