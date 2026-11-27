"""Compare a pruned binary syndrome trellis against native unary contractions."""
from math import prod

from trace_histogram import histogram


def echelon(vectors):
    pivots = {}
    for value in vectors:
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = value
                break
            value ^= pivots[pivot]
    return pivots


def contains(pivots, vector):
    while vector:
        pivot = vector.bit_length() - 1
        if pivot not in pivots:
            return False
        vector ^= pivots[pivot]
    return True


def coset_value(columns, target, weights, modulus):
    suffixes = [echelon(columns[j:]) for j in range(len(columns) + 1)]
    if not contains(suffixes[0], target):
        return 0, 0
    states = {0: 1}
    peak = 1
    for j, (column, endpoints) in enumerate(zip(columns, weights)):
        new = {}
        for current, value in states.items():
            for bit, weight in enumerate(endpoints):
                after = current ^ (column if bit else 0)
                if contains(suffixes[j + 1], target ^ after):
                    new[after] = (new.get(after, 0) + weight * value) % modulus
        states = new
        peak = max(peak, len(new))
    return states.get(target, 0), peak


def scattered_checks(m):
    columns = []
    for i in range(m):
        columns.extend([(1 << i) ^ ((1 << (i-1)) if i else 0), 1 << i])
    return columns


def word(s, theta, m):
    bits = []
    for i in range(m):
        bit = (s >> i) & 1
        neighbor = (s >> (i+1)) & 1
        bits.extend((bit, bit ^ neighbor ^ theta))
    return bits


def check():
    from torus_carry_count import point_count
    from punctured_witness import BinaryField
    from frobenius_drift import power

    field = BinaryField(7)
    q, m = field.size, field.m
    curve = {(1, 2): 1, (1, 1): 1, (0, 0): 1}
    signed = point_count(field, curve) - (q-1)
    quotient = histogram(1, lambda mask: signed if mask else q-1)
    direct_theta = []
    for t in range(1, q):
        inv = power(field, t, q-2)
        direct_theta.append(inv ^ field.mul(inv, inv))
    assert quotient == {bit: direct_theta.count(bit) for bit in set(direct_theta)}
    checks = scattered_checks(m)
    for modulus in (8, 32, 128):
        for w in range(modulus):
            unary = [(3+j + (2*j+1)*(1-w), (2*j+1)*w) for j in range(2*m)]
            base = pow(w*(2-w), 2*m, modulus)
            answer = sum(n*coset_value(checks, ((1<<m)-1)*bit, unary, modulus)[0]
                         for bit,n in quotient.items()) * base % modulus
            direct = sum(prod(weights[bit] for weights,bit in zip(unary,word(s,theta,m)))
                         for theta in direct_theta for s in range(q)) * base % modulus
            assert answer == direct
    for m in (5, 16, 64, 100):
        cols = scattered_checks(m)
        for target in (0, (1<<m)-1):
            value, peak = coset_value(cols,target,[(1,1)]*(2*m),2**(m+2))
            assert value == 2**m and peak <= 2
    print("AS quotient histogram",quotient,"; 168 modular scalars; 100 free bits with at most 2 states")

if __name__ == "__main__":
    check()
