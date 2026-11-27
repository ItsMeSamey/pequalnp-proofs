"""Verify a neutral two-tag routing certificate and decide indexed wedge existence."""
from itertools import combinations
from central_uplift import combine
from component_nullity import bits, dependencies
from omega_lift_hitting import solve


def routed(private, tags, omega, neutral_ids, routing_basis, baseline=None):
    """Invalid certificates raise ValueError. Return a witness or None."""
    n = len(private)
    neutral = list(neutral_ids)
    basis = list(routing_basis)
    if any(type(i) is not int or i not in range(n) for i in neutral) or len(set(neutral)) != len(neutral):
        raise ValueError("invalid neutral IDs")
    if dependencies(basis):
        raise ValueError("dependent routing basis")
    cycles = dependencies(private)
    if baseline is None:
        baseline = [0]*n
    if len(tags)!=n or len(baseline)!=n or any(v not in range(4) for v in [*tags,*baseline]):
        raise ValueError("invalid labels")
    if any(combine(baseline,z) for z in cycles):
        raise ValueError("nonlinear baseline")
    residual = [t^b for t,b in zip(tags,baseline)]
    if any(residual[i] for i in neutral):
        raise ValueError("non-neutral router tag")
    directions = {private[i] for i in neutral}
    for size in (1,2,3):
        for selected in combinations(basis,size):
            v = 0
            for a in selected:
                v ^= a
            if v not in directions:
                raise ValueError("missing routing direction")
    for local in dependencies([private[i] for i in neutral]):
        word = sum(1<<neutral[j] for j in bits(local))
        if any(omega(word,other) for other in cycles):
            raise ValueError("neutral cycle outside indexed radical")
    r = n-len(cycles)
    result = solve(private,residual,omega,min(r,2*(r-len(basis))+6))
    if result is not None:
        result.predictions = [t^b for t,b in zip(result.predictions,baseline)]
        for ids in (result.x,result.y):
            if combine(tags,sum(1<<i for i in ids)):
                raise ArithmeticError("original tag replay failed")
    return result
