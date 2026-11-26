"""Exhaust all binary three-port tables, retaining XOR base at each table."""
from itertools import permutations, product


def mul(x,y):
    r = 0
    while y:
        if y & 1:
            r ^= x
        x <<= 1
        if x & 4:
            x ^= 7
        y >>= 1
    return r


def determinant(m, selected):
    d = 0
    for perm in permutations(selected):
        v = 1
        for i,j in zip(selected,perm):
            v = mul(v,m[i][j])
        d ^= v
    return d


def represent(bits):
    base = next(i for i,c in enumerate(bits) if c)
    f = [bits[i ^ base] for i in range(8)]
    m = [[0]*3 for _ in range(3)]
    d = [f[1<<i] for i in range(3)]
    for i in range(3):
        m[i][i] = d[i]
    cycle = [(0,1),(1,2),(2,0)]
    p = [f[1<<i | 1<<j] ^ d[i]*d[j] for i,j in cycle]
    t = f[7] ^ d[0]*d[1]*d[2] ^ p[0]*d[2] ^ p[1]*d[0] ^ p[2]*d[1]
    if all(p):
        z = next(z for z in (1,2,3) if mul(z,z) ^ mul(t,z) ^ 1 == 0)
        forward = [1,1,z]
    else:
        forward = [1]*3
        forward[p.index(0)] = t
    for k,(i,j) in enumerate(cycle):
        m[i][j] = forward[k]
        m[j][i] = (next(a for a in range(4) if mul(forward[k],a)==p[k])
                   if forward[k] else 0)
    assert all(determinant(m,[i for i in range(3) if x>>i&1]) == f[x] for x in range(8))
    return base,m


if __name__ == '__main__':
    count = 0
    for bits in product(range(2), repeat=8):
        if any(bits):
            represent(bits)
            count += 1
    print(f'{count} nonzero binary three-port tables, all 2040 coefficients verified')
