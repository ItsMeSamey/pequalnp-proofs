"""Compile a native closed network to forbidden cycles of length two or three."""
from itertools import permutations
from one_long_forbidden_cycle import cycles, forbidden


def compile_network(sigma):
    n = len(sigma)
    if n % 3 or sorted(sigma) != list(range(n)):
        raise ValueError("expected a permutation in triples")
    f = forbidden(sigma)
    for orbit in cycles(f):
        tip = orbit[0]
        for i in range(1, len(orbit)-2):
            other = orbit[i]
            x = len(f)
            y, z = x+1, x+2
            f[tip] = other
            f[other] = x
            f.extend([tip, orbit[i+1], z])
            f[orbit[-1]] = y
            tip = y
    out = [f[i-i%3+(i+1)%3] for i in range(len(f))]
    for i in range(len(f)):
        if f[i] == i:
            j = len(out)
            out[i-i%3+(i-1)%3] = j
            out.extend([j+2,j+1,i])
    return out


def projected_cycles(sigma, mask, n):
    perm = [sigma[i-i%3+(i+(mask>>(i//3)&1))%3] for i in range(len(sigma))]
    return [tuple(i for i in c if i<n) for c in cycles(perm) if min(c)<n]


if __name__ == '__main__':
    cases = list(permutations(range(3))) + list(permutations(range(6)))
    tests = 0
    for sigma in cases:
        n = len(sigma)
        out = compile_network(sigma)
        c = cycles(forbidden(sigma))
        new = 2*sum(max(0,len(o)-3) for o in c) + sum(len(o)==1 for o in c)
        if len(out)!=n+3*new or any(len(o) not in (2,3) for o in cycles(forbidden(out))):
            raise AssertionError(sigma)
        for m in range(1<<(n//3)):
            expected = projected_cycles(sigma,m,n)
            for extra in range(1<<new):
                if projected_cycles(out,m+(extra<<(n//3)),n)!=expected:
                    raise AssertionError((sigma,m,extra))
                tests+=1
    print(len(cases), 'networks;', tests, 'mask lifts')
