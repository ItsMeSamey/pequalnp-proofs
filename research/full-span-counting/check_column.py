"""Check adaptive any-degree feature discovery on arbitrary weighted Boolean profiles."""
from fractions import Fraction as F
from random import Random
from sympy import Matrix


def solve(m, rows):
    truth = lambda s, u: int(u & s == s)
    cols = []
    coef = []
    degrees = []
    loss_before = None
    while True:
        err = {u: 1-sum(a*truth(s,u) for s,a in zip(cols,coef)) for u in rows}
        weights = {u: c*u.bit_count() for u,c in rows.items()}
        loss = lambda s: sum(weights[u]*err[u]**2*truth(s,u) for u in rows)
        if loss_before is not None:
            assert loss(0) < loss_before
        if not loss(0):
            break
        loss_before = loss(0)
        s = 0
        for i in range(m):
            candidate = s | (1 << i)
            if loss(candidate):
                s = candidate
        assert s != 0 and s not in cols
        corr = lambda a: sum(weights[u]*err[u]*truth(a,u) for u in rows)
        assert corr(s) != 0
        assert {u for u in rows if weights[u] and err[u] and truth(s,u)} == {s}
        # Optional correlation-preserving deletion. The final column stays independent.
        for i in range(m):
            candidate = s & ~(1 << i)
            if candidate and corr(candidate):
                s = candidate
        cols.append(s)
        degrees.append(s.bit_count())
        mu = lambda a: sum(weights[u]*truth(a,u) for u in rows)
        gram = Matrix([[mu(a|b) for a in cols] for b in cols])
        coef = list(map(F, gram.inv()*Matrix([mu(a) for a in cols])))
    assert len(cols) <= sum(bool(u and c) for u,c in rows.items())
    return degrees


def main():
    rng = Random(678)
    cases = []
    for m in range(1,6):
        for _ in range(12):
            rows = {u:rng.randrange(4) for u in range(1<<m)}
            cases.append(solve(m, rows))
    # On the entire cube, representing OR requires every nonempty monomial.
    assert max(solve(4, {u:1 for u in range(16)})) == 4
    print(f"{len(cases)+1} cases passed, including full-cube degree-four discovery.")


if __name__ == '__main__':
    main()
