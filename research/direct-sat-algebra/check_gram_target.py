from itertools import product
from unittest.mock import patch
import gram_target
from quadratic_image import Quadratic, evaluate, parity


def check():
    pair = ((0, 1),)
    indicators = [Quadratic(1, 3, pair), Quadratic(0, 1, pair),
                  Quadratic(0, 2, pair), Quadratic(0, 0, pair)]
    values = [evaluate(indicators, x) for x in range(4)]
    assert sorted(values) == [1, 2, 4, 8]
    target = 7
    assert all(any(parity(s & y) == parity(s & target) for y in values) for s in range(16))
    # Genuine independent AND ports make the image 4*2^p and joint radical zero.
    p = 8
    padded = indicators + [Quadratic(pairs=((2 + 2*j, 3 + 2*j),)) for j in range(p)]
    with patch.object(gram_target, "gauss", wraps=gram_target.gauss) as observed:
        r = gram_target.probe(2 + 2*p, padded, target)
    assert observed.call_count == r.phase_evals and r.reason == "annihilator"
    def relation(y):
        return sum(a * (-1 if parity(s & y) else 1)
                   for s, a in zip(r.dictionary, r.annihilator))
    assert relation(target) and all(relation(y | (z << 4)) == 0 for y in values for z in range(1 << p))
    sub = indicators[1:3]
    r = gram_target.probe(2, sub, 3)
    assert r.reason == "integer bound" and r.count_upper == 0
    assert gram_target.probe(2, indicators, target, max_phase_evals=1).reason == "budget"
    cases = 0
    for fs in product(indicators, repeat=2):
        for dictionary in (None, (), (1,), (1, 1, 3), (0, 3, 1, 2)):
            for t in range(4):
                count = sum(evaluate(fs, x) == t for x in range(4))
                r = gram_target.probe(2, fs, t, dictionary)
                assert r.status in ("UNSAT", "UNKNOWN", "SAT") and r.count_upper >= count
                assert r.status != "UNSAT" or count == 0
                if r.status == "SAT":
                    assert r.count == count and evaluate(fs, r.witness) == t
                cases += 1
    # The selector bit separates a single attained output from 2^p others.
    gated = [Quadratic(linear=1)] + [
        Quadratic(pairs=((0, i),)) for i in range(1, p + 1)
    ]
    r = gram_target.probe(p + 1, gated, 0)
    assert r.status == "SAT" and r.count == (1 << p) and evaluate(gated, r.witness) == 0
    with patch.object(gram_target, "gauss", wraps=gram_target.gauss) as calls:
        limited = gram_target.probe(p + 1, gated, 0, max_phase_evals=r.phase_evals - 1)
        assert limited.status == "UNKNOWN" and calls.call_count == limited.phase_evals
        assert limited.phase_evals == r.phase_evals - 1
    even = [Quadratic(linear=v) for v in (1, 2, 4, 7)]
    absent = gram_target.probe(3, even, 1)
    assert absent.status == "UNKNOWN" and absent.count_upper >= 1
    print(f"{cases} exhaustive Gram controls and padded/Christoffel/budget checks passed")


if __name__ == "__main__":
    check()
