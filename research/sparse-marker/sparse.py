"""Deterministic singleton-marker SAT under a selector-polynomial sparsity bound."""
from itertools import combinations, count
from math import isqrt


def times(a, b):
    value = 0
    while b:
        bit = b & -b
        value ^= a << (bit.bit_length() - 1)
        b ^= bit
    return value


def exact_quotient(value, divisor):
    quotient = 0
    while value and value.bit_length() >= divisor.bit_length():
        shift = value.bit_length() - divisor.bit_length()
        quotient ^= 1 << shift
        value ^= divisor << shift
    if value:
        raise ArithmeticError("inexact polynomial division")
    return quotient


def det(matrix):
    """Fraction-free elimination in GF(2)[T], polynomial coefficients as bitsets."""
    a = [row[:] for row in matrix]
    n = len(a)
    previous = 1
    for i in range(n - 1):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return 0
        a[i], a[pivot] = a[pivot], a[i]
        for j in range(i + 1, n):
            for k in range(i + 1, n):
                numerator = times(a[i][i], a[j][k]) ^ times(a[j][i], a[i][k])
                a[j][k] = exact_quotient(numerator, previous)
        previous = a[i][i]
    return a[-1][-1] if a else 1


def weighted_sum(rows, marker, weights):
    n = len(rows)
    coefficients = []
    constants = []
    for i, (left, right) in enumerate(weights):
        constants.append(left ^ right)
        coefficients.append([(left if i == j else 0) ^ (right if rows[i] >> j & 1 else 0)
                             for j in range(n)])
    constants.append(0)
    coefficients.append([(marker >> j) & 1 for j in range(n)])
    total = 0
    for i, c in enumerate(constants):
        if c:
            total ^= times(c, det(coefficients[:i] + coefficients[i+1:]))
    for i, k in combinations(range(n+1), 2):
        for j in range(n):
            factor = times(coefficients[i][j], coefficients[k][j])
            if factor:
                remaining = [row[:j] + row[j+1:] for h,row in enumerate(coefficients)
                             if h != i and h != k]
                total ^= times(factor, det(remaining))
    return total


def solve(rows, marker, sparsity):
    """Return a witness or None. Rejection assumes the advertised upper bound."""
    n = len(rows)
    if sparsity < 1:
        raise ValueError("use a positive sparsity upper bound")
    primes = (p for p in count(2) if all(p % k for k in range(2, isqrt(p)+1)))
    for _ in range(n*(sparsity-1)+1):
        p = next(primes)
        weights = [(1, 1 << pow(2, i, p)) for i in range(n)]
        if not weighted_sum(rows, marker, weights):
            continue
        for i in range(n):
            weights[i] = (1,0)
            if not weighted_sum(rows, marker, weights):
                weights[i] = (0,1)
        # Solve the selected n homogeneous equations plus marker=1 by row reduction.
        system = [rows[i] if r else (1 << i) for i, (_,r) in enumerate(weights)]
        system.append(marker | (1 << n))
        for j in range(n):
            k = next(i for i in range(j,n+1) if system[i] >> j & 1)
            system[j], system[k] = system[k], system[j]
            for i in range(n+1):
                if i != j and system[i] >> j & 1:
                    system[i] ^= system[j]
        return sum(((system[i] >> n) & 1) << i for i in range(n))
    return None
