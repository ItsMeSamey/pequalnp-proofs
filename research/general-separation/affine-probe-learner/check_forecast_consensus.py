"""Finite full-query consensus and masking controls. Standard library only."""
from itertools import combinations, permutations


def majority(q,V,tie):
    assert tie & V == tie and tie.bit_count() == 1
    margin = 2*(q & V).bit_count()-V.bit_count()
    return int(bool(q & tie) if margin == 0 else margin > 0)


def degree(fields,V):
    for k in range(1,4):
        for group in combinations(set(fields),k):
            common = V
            for side in group:
                common &= side
            if not common:
                return k-1
    return 3


def profiles():
    for m in range(1,4):
        V = (1 << m)-1
        count = 0
        for policy in range(1 << (1 << m)):
            sides = [q if policy >> q & 1 else V ^ q for q in range(1 << m)]
            joint = V
            for side in sides:
                joint &= side
            assert (degree(sides,V) == 3) == bool(joint)
            count += bool(joint)
        assert count == m
    for V in range(1,64):
        for i in range(6):
            tie = 1 << i
            if not tie & V:
                continue
            selected = {(q if majority(q,V,tie) else ~q)&V for q in range(64)}
            assert all(selected) and all(a & b for a,b in combinations(selected,2))
    selected = [q if majority(q,7,1) else 7 ^ q for q in range(8)]
    assert degree(selected,7) == 2 and {3,5,6} <= set(selected)
    # Independent tie-to-one predictions on the two complementary singletons.
    chosen = [q for q in (1,2) if 2*q.bit_count() >= 2]
    assert len(chosen) == 2 and not (chosen[0] & chosen[1])
    # An external tie seed can likewise disagree with all live words jointly.
    V,tie = 3,4
    q1,q2 = 5,6
    assert q1 & tie and q2 & tie and not (q1 & q2 & V)
    assert (V & q1).bit_count() == (V & q2).bit_count() == 1


def removals(n,order):
    V = (1 << (1 << n))-1
    history = []
    for chosen in order[:-1]:
        singleton = 1 << chosen
        assert singleton & V
        # A predictor represented by chosen says one on its own singleton.
        history.append((singleton,0))
        V ^= singleton
    assert len(history) == (1 << n)-1 and V == 1 << order[-1]
    assert all(bool(q & V) == bool(y) for q,y in history)


def decode(n,x):
    bits = [(x >> (4*n-1-i)) & 1 for i in range(4*n)]
    out = 0
    for i in range(n):
        a,c,e = bits[3*i:3*i+3]
        out = 2*out+(a ^ bits[3*n+i] ^ (c & e))
    return out


def projected():
    for n in (1,2):
        size = 1 << n
        fibers = [0]*size
        for x in range(1 << (4*n)):
            fibers[decode(n,x)] |= 1 << x
        assert all(f.bit_count() == 1 << (3*n) for f in fibers)
        pull = [sum(fibers[i] for i in range(size) if mask >> i & 1)
                for mask in range(1 << size)]
        for F in range(1,1 << size):
            for i in range(size):
                if F >> i & 1:
                    raw_tie = fibers[i] & -fibers[i]
                    assert all(majority(q,F,1 << i) == majority(pull[q],pull[F],raw_tie)
                               for q in range(1 << size))
        if n == 2:
            # All three forecasts come from the SAME F=1 posterior.
            choices = [pull[q] & pull[7] for q in (3,5,6)]
            assert all(majority(q,pull[7],1) for q in choices)
            assert all(a & b for a,b in combinations(choices,2))
            assert not (choices[0] & choices[1] & choices[2])


if __name__ == '__main__':
    profiles()
    for n in range(3):
        for order in permutations(range(1 << n)):
            removals(n,order)
    removals(3,list(reversed(range(8))))
    projected()
    print('Finite consensus, singleton-removal and masked-state checks passed.')
