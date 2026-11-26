"""Exact three-OR decision for P6 on its five edge and ten edge-pair patterns."""
from itertools import combinations

edges = [3 << i for i in range(5)]
positive = sorted({a | b for a, b in combinations(edges, 2)})
tests = edges + positive
negative_bits = (1 << len(edges)) - 1
required = ((1 << len(positive)) - 1) << len(edges)
full = required | negative_bits

def initial_bank():
    bank = {full}
    for i in range(6):
        literal = sum(1 << j for j, test in enumerate(tests) if test >> i & 1)
        bank |= {signal & literal for signal in bank}
    return bank

def possible_new_ors(bank):
    return {a | b for a, b in combinations(bank, 2)} - bank

def extend(bank, new_or):
    return bank | {a & new_or for a in bank}

def finish_with_at_most_one_or(bank):
    residual = full
    for signal in bank:
        if required & ~signal == 0:
            residual &= signal
    remaining_negatives = residual & negative_bits
    if remaining_negatives == 0:
        return True
    candidates = [s for s in bank if s & remaining_negatives == 0]
    return any(required & ~(a | b) == 0 for a, b in combinations(candidates, 2))

def four_or(bits):
    a,b,c,d,e,f = [bool(bits >> i & 1) for i in range(6)]
    return ((a | e) & c) | ((b | f) & d) | (a & e)

if __name__ == '__main__':
    assert len(positive) == 10
    assert all(not four_or(bits) for bits in edges)
    assert all(four_or(bits) for bits in positive)
    base = initial_bank()
    assert not finish_with_at_most_one_or(base)
    two_steps = 0
    for h in sorted(possible_new_ors(base)):
        one = extend(base, h)
        assert not finish_with_at_most_one_or(one)
        for j in sorted(possible_new_ors(one)):
            two_steps += 1
            assert not finish_with_at_most_one_or(extend(one, j))
    print(f"{len(base)} raw conjunctions, {len(possible_new_ors(base))} first ORs, "
          f"{two_steps} ordered two-OR banks; no three-OR decoder. Four-OR control passed.")
