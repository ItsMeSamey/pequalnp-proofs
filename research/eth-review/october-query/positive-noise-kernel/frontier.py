"""Evaluate real ports (packet, occurrence bit, gate, literal sign) in supplied order."""
from fractions import Fraction
from collections import defaultdict
from itertools import product


def contract(ports, kinds, length, t):
    t = Fraction(t)
    first, last, size = {}, {}, defaultdict(int)
    for i, port in enumerate(ports):
        for key in enumerate(port[:3]):
            first.setdefault(key, i)
            last[key] = i
            size[key] += 1
    absent = [g for g in kinds if (2, g) not in first]
    if any(kinds[g] == "or" for g in absent):
        return 0
    states, live = {(): 2**len(absent)}, []
    for i, (p, e, g, positive) in enumerate(ports):
        pk, ek, gk = (0,p), (1,e), (2,g)
        new = [key for key in (pk,ek,gk) if first[key] == i]
        keep = [key for key in live + new if last[key] > i]
        choices = [range(size[key]+1) if key == pk else range(2) for key in new]
        updated = defaultdict(Fraction)
        for state, weight in states.items():
            for extra in product(*choices):
                env = dict(zip(live, state))
                for key, val in zip(new, extra):
                    env[key] = (val,0) if key == pk else val
                total, seen = env[pk]
                x, mode = env[ek], env[gk]
                seen += x
                if seen > total or (last[pk] == i and seen != total):
                    continue
                env[pk] = total, seen
                q = (1-t)*x + t*Fraction(total,length)
                if kinds[g] == "copy":
                    factor = q if mode else 1-q
                else:
                    factor = (1-q if positive else q) if mode else 1
                    if mode and first[gk] == i:
                        factor = -factor
                updated[tuple(env[key] for key in keep)] += weight*factor
        states, live = updated, keep
    return states.get((), 0)
