#!/usr/bin/env python3
"""Finite checks for Q8 acting separately on C3,C5 and for Q8 action slices."""
from itertools import product

# (sign, basis) denotes ±1, ±i, ±j, ±k in Hamilton's convention.
Q = list(product((1, -1), range(4)))
ONE, I, J = (1, 0), (1, 1), (1, 2)
TABLE = ((1, 2, 3, 4), (2, -1, 4, -3), (3, -4, -1, 2), (4, 3, -2, -1))


def mul(a, b):
    v = TABLE[a[1]][b[1]]
    return a[0] * b[0] * (1 if v > 0 else -1), abs(v) - 1


def inv(a):
    return (a[0] if a[1] == 0 else -a[0]), a[1]


def power(a, k):
    z = ONE
    for _ in range(k % 4):
        z = mul(z, a)
    return z


def compose(g, h):
    r, s, q = g
    u, v, t = h
    return ((r + (-1 if q[1] & 1 else 1)*u) % 3,
            (s + (-1 if q[1] & 2 else 1)*v) % 5, mul(q, t))


IDENTITY = (0, 0, ONE)
GROUP = list(product(range(3), range(5), Q))
# Independent brute inverse lookup in the multiplication table.
INVERSE = {g: next(h for h in GROUP if compose(g, h) == IDENTITY) for g in GROUP}
WORDS = (((0, 1), (1, -1), (0, -1), (1, 1)),
         ((1, -1), (0, -1), (1, -1), (0, 1), (0, 1)))


def brute(word, args):
    g = IDENTITY
    for j, sign in word:
        g = compose(g, args[j] if sign == 1 else INVERSE[args[j]])
    return g


def prefix_formula(word, args):
    r = s = 0
    u = v = 0
    h = ONE
    for j, sign in word:
        a, b, q = args[j]
        p, t = q[1] & 1, (q[1] >> 1) & 1
        # Inverse letters use the updated quotient switches for their coefficients.
        r += sign * (-1)**(u ^ (p if sign < 0 else 0)) * a
        s += sign * (-1)**(v ^ (t if sign < 0 else 0)) * b
        u ^= p
        v ^= t
        h = mul(h, q if sign == 1 else inv(q))
    return r % 3, s % 5, h


def check_slices():
    count = 0
    # Q8 acts faithfully by regular permutation. Check actual group prefixes in Q8.
    word = WORDS[1]
    for varying, other in ((I,J), (J,I)):
        for frozen in product(range(4), repeat=2):
            def prefixes(x):
                args = [mul(power(I, x[j]), power(J, frozen[j])) if varying == I
                        else mul(power(I, frozen[j]), power(J, x[j])) for j in range(2)]
                history = [ONE]
                for j, sign in word:
                    q = args[j] if sign == 1 else inv(args[j])
                    history.append(mul(history[-1], q))
                return history
            base = prefixes((0,0))
            exp = {power(varying, i): i for i in range(4)}
            def differences(x):
                return [exp[mul(z,inv(c))] for z,c in zip(prefixes(x), base)]
            a, b = differences((1,0)), differences((0,1))
            for x,y in product(range(4), repeat=2):
                assert differences((x,y)) == [(x*u+y*v) % 4 for u,v in zip(a,b)]
                count += len(base)
    return count


def main():
    lifts = {(a,b,mul(mul(power(I, u), power(J, v)), (-1 if k else 1, 0)))
             for a,b,u,v,k in product(range(3),range(5),range(2),range(2),range(2))}
    assert lifts == set(GROUP)
    assert {mul(power(I,a),power(J,b)) for a,b in product(range(4),repeat=2)} == set(Q)
    count = 0
    for args in product(GROUP, repeat=2):
        for word in WORDS:
            assert brute(word, args) == prefix_formula(word,args)
            count += 1
    print(f'passed {len(lifts)} lifted elements, {count} word evaluations, {check_slices()} prefix-slice checks')


if __name__ == '__main__':
    main()
