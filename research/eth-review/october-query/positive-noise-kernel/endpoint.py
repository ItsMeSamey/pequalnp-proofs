"""Evaluate the complete packet-noise endpoint using joint source populations."""
from collections import Counter, defaultdict
from fractions import Fraction


def endpoint(ports, kinds, length):
    packets = list(dict.fromkeys(p for p, _, _, _ in ports))
    index = {p: i for i, p in enumerate(packets)}
    shifts = defaultdict(Counter)
    for p, e, _, _ in ports:
        shifts[e][index[p]] += 1
    table = {(0,)*len(packets): 1}
    for shift in shifts.values():
        result = table.copy()
        for state, count in table.items():
            target = list(state)
            for coordinate, increment in shift.items():
                target[coordinate] += increment
            target = tuple(target)
            result[target] = result.get(target, 0) + count
        table = result
    numerator = 0
    for state, count in table.items():
        terms = {g: [1, 1, 1] for g in kinds}
        for p, _, g, positive in ports:
            ones = state[index[p]]
            zeros = length - ones
            term = terms[g]
            if kinds[g] == "copy":
                term[0] *= ones
                term[1] *= zeros
            else:
                term[1] *= zeros if positive else ones
                term[2] *= length
        product = count
        for g, (a, b, scale) in terms.items():
            product *= a+b if kinds[g] == "copy" else scale-b
        numerator += product
    return Fraction(numerator, length**len(ports))
