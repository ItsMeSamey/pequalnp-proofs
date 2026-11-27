"""Full origin at the single center -L with shift L; bounded CNF fixture."""
from collections import Counter
from itertools import product
from math import prod


def kernel(length, displacement, modulus):
    """Integral ordinary coefficients after exact cancellation of denominator twos."""
    grid = range(-length, length)
    coeff = [1]
    for q in grid:
        if q == displacement:
            continue
        nxt = [0] * (len(coeff) + 1)
        for i, a in enumerate(coeff):
            nxt[i] += (-length - q) * a
            nxt[i + 1] += length * a
        coeff = nxt
    den = prod(-q for q in grid if q)
    twos = abs(den) & -abs(den)
    assert all(a % twos == 0 for a in coeff)
    inv = pow(den // twos, -1, modulus)
    return [(a // twos) * inv % modulus for a in coeff]


def count(clauses, declared, length, precision):
    # This fixture covers original variable degrees 1 and 2; degree>2 needs an EQ tree.
    if length < 2 or length & (length - 1) or precision < 1:
        raise ValueError("invalid packet or precision")
    occurrences = [(abs(lit), lit) for c in clauses for lit in c]
    if any(not 1 <= var <= declared for var, _ in occurrences):
        raise ValueError("undeclared literal")
    E = len(occurrences)
    M = 2 * E
    if E > 10 or M % length:
        raise ValueError("fixture size or equal-packet requirement")
    ctr = Counter()
    degree = M * (2 * length - 1)
    J = min(degree, M + precision - 1)
    mod = 1 << precision
    zero = (0,) * (J + 1)
    one = (1,) + zero[1:]
    def add(a, b, sign=1):
        return tuple((x + sign * y) % mod for x, y in zip(a, b))
    def multiply(a, b):
        ctr["polynomial_products"] += 1
        out = [0] * (J + 1)
        for i, x in enumerate(a):
            if x:
                for j in range(J + 1 - i):
                    ctr["coefficient_visits"] += 1
                    out[i + j] = (out[i + j] + x * b[j]) % mod
        return tuple(out)
    # Subdivide every original edge: ports 2e,2e+1 read one logical COPY2 bit.
    # The first is the old clause-side row, the second the variable-tensor row.
    K = {}
    for d in range(1-length, length):
        coeff = kernel(length, d, mod)
        K[d] = tuple((coeff + [0]*(J+1))[:J+1])
    var_ports = [[2*i + 1 for i, (v, _) in enumerate(occurrences) if v == k]
                 for k in range(1, declared+1)]
    if any(len(group)>2 for group in var_ports):
        raise ValueError("degree above 2")
    unused = sum(not group for group in var_ports)
    result = zero
    for bits in product((0, 1), repeat=E):
        ctr["physical_copy_assignments"] += 1
        rows = []
        for slot in range(M):
            packet = slot // length * length
            z = zero
            for y in range(packet, packet+length):
                if bits[y//2]:
                    z = add(z, K[y-slot])
            rows.append(z)
        term = one
        edge = 0
        for clause in clauses:
            bad = one
            for lit in clause:
                z = rows[2*edge]
                bad = multiply(bad, add(one,z,-1) if lit>0 else z)
                edge += 1
            term = multiply(term, add(one,bad,-1))
        for group in var_ports:
            if len(group)==2:
                x,y = (rows[i] for i in group)
                eq = add(multiply(x,y), multiply(add(one,x,-1),add(one,y,-1)))
                term = multiply(term,eq)
        result = add(result,term)
    coefficients = tuple((j << unused) % mod for j in result)
    return sum(coefficients) % mod, coefficients, dict(ctr), degree


def raw(clauses, declared):
    return sum(all(any(assignment[abs(lit)-1] == (lit>0) for lit in c)
                   for c in clauses) for assignment in product((0,1), repeat=declared))


if __name__ == "__main__":
    fixtures = (((1,2,3),(-1,-2,-3)), ((1,2,3),(-1,),(-2,),(-3,)))
    for clauses in fixtures:
        expected = raw(clauses,3)
        for p in (1,4):
            result, coeff, work, degree = count(clauses,3,4,p)
            assert result == expected % (1<<p)
            print(dict(clauses=clauses,p=p,raw=expected,recovered=result,
                       retained_orders=len(coeff),full_degree=degree,
                       coefficients=coeff,work=work))
