"""Independent ground truth from counting exact residual functions in every order."""
from itertools import permutations
from random import Random
from two_state_any_order import recognize
from two_state_other_order import value


def truth_program(n, truth):
    widths = [1 << i for i in range(n+1)]
    layers = [tuple(tuple(1 << (j+(b<<i)) for j in range(1<<i))
                    for b in range(2)) for i in range(n)]
    return widths, 1, layers, truth


def allowed(n, truth, order):
    words = {tuple(truth >> sum(((i>>j)&1)<<v for j,v in enumerate(order)) & 1
                   for i in range(1<<n))}
    for _ in order:
        words = {word[b::2] for word in words for b in (0,1)}
        if len(words)>2:
            return False
    return True


if __name__ == '__main__':
    rng = Random(175)
    yes = no = missed_by_fixed = 0
    for n in range(6):
        identity = list(range(n))
        tables = range(1 << (1<<n)) if n<=3 else [rng.getrandbits(1<<n) for _ in range(180)]
        for truth in tables:
            program = truth_program(n, truth)
            det, order, cost = recognize(program, identity)
            exists = any(allowed(n,truth,o) for o in permutations(identity))
            assert (det is not None) == exists
            if exists:
                yes += 1
                missed_by_fixed += not allowed(n,truth,identity)
                assert all(value(det,order,x)==(truth>>x & 1) for x in range(1<<n))
            else:
                no += 1
    print(yes,no,missed_by_fixed)
