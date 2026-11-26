"""Reproduce the chain-ring stratum formula by binary elimination and enumeration."""

from fractions import Fraction
from itertools import product
from math import prod
from random import Random


def poly_mul(a, b):
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        b >>= 1
    return value


def reduce_poly(a, modulus):
    while a.bit_length() >= modulus.bit_length():
        a ^= modulus << (a.bit_length() - modulus.bit_length())
    return a


def constraints_for_ideal(block, power, n):
    # Remainder modulo f^v is linear in the n coefficients of the input.
    columns = [reduce_poly(1 << j, power) for j in range(n)]
    return [(sum(((c >> bit) & 1) << (block*n+j) for j, c in enumerate(columns)), 0)
            for bit in range(power.bit_length()-1)]


def affine_size(rows, width):
    basis = {}
    for coeff, rhs in rows:
        while coeff:
            pivot = coeff.bit_length()-1
            if pivot not in basis:
                basis[pivot] = coeff, rhs
                break
            other, value = basis[pivot]
            coeff ^= other
            rhs ^= value
        else:
            if rhs:
                return 0
    return 1 << (width-len(basis))


def stratum_count(f, k, b, h, rows):
    d = f.bit_length()-1
    n = d*k
    width = (b+h)*n
    powers = [1]
    for _ in range(k):
        powers.append(poly_mul(powers[-1], f))

    def filtered(vx, vz):
        extra = []
        for block in range(b+h):
            power = powers[vx if block < b else vz]
            extra.extend(constraints_for_ideal(block, power, n))
        return affine_size(rows+extra, width)

    total = filtered(k, k) << (b*h*n)
    for v in range(k):
        size = filtered(v, v)-filtered(v+1, v)
        total += size << (h*((b-1)*n+d*v))
    return total


def brute_count(f, k, b, h, rows):
    modulus = 1
    for _ in range(k):
        modulus = poly_mul(modulus, f)
    n = modulus.bit_length()-1
    alphabet = range(1 << n)
    times = [[reduce_poly(poly_mul(a, c), modulus) for c in alphabet] for a in alphabet]
    total = 0
    for xs in product(alphabet, repeat=b):
        for ys in product(alphabet, repeat=b*h):
            zs = [0]*h
            for j in range(h):
                for i, x in enumerate(xs):
                    zs[j] ^= times[x][ys[b*j+i]]
            vector = sum(z << (n*i) for i,z in enumerate((*xs,*zs)))
            total += all((vector & mask).bit_count()%2 == rhs for mask,rhs in rows)
    return total


def packet_test():
    # True Cauchy entry for the balanced grid S={-L,...,L-1}.
    length = 8
    grid = range(-length,length)
    node = 2*length+1
    w = Fraction(prod(node-t for t in grid),node*prod(-t for t in grid if t))
    kernel = ((1,1-w),(0,w))
    for x,y in product(range(2),repeat=2):
        assert kernel[y][x]*kernel[1-y][1-x] == w*(x==y)


if __name__ == '__main__':
    rng = Random(3547)
    cases = 0
    for f,k,b,h in [(2,2,2,2),(2,3,2,1),(2,4,1,2),(7,2,1,2)]:
        width = (b+h)*k*(f.bit_length()-1)
        systems = [[], [(0,1)], [(1,0),(1,1)]]
        for _ in range(7):
            systems.append([(rng.getrandbits(width),rng.randrange(2)) for _ in range(4)])
        for rows in systems:
            assert stratum_count(f,k,b,h,rows) == brute_count(f,k,b,h,rows)
            cases += 1
    packet_test()
    print(f'{cases} chain-ring systems and four balanced wire entries passed')
