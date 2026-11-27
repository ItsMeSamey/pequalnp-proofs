"""Independent original-coordinate controls for the odd mask SAT encoding."""
from itertools import combinations

from joint_fault_solver import solve
from odd_masked_circuit import compile_source, decode, lift


def evaluate(n,F,x):
    gates,out = F
    values = {-1:0,-2:1}
    for i in range(n):
        values[i] = (x >> (n-i-1)) & 1
    for w,(u,v) in enumerate(gates,n):
        assert u in values and v in values
        values[w] = int(not (values[u] and values[v]))
    return values[out]


def original_decode(n,x):
    bits = tuple((x >> i) & 1 for i in reversed(range(4*n)))
    out = 0
    for i in range(n):
        a,c,e = bits[3*i:3*i+3]
        out = 2*out + (a ^ bits[3*n+i] ^ (c & e))
    return out


def source(n,mask):
    # Explicit DNF with one minterm per selected word.
    gates = []
    def nand(u,v):
        gates.append((u,v))
        return n+len(gates)-1
    def neg(u):
        return nand(u,u)
    def both(u,v):
        return neg(nand(u,v))
    out = -1
    for word in range(1 << n):
        if (mask >> word) & 1:
            term = -2
            for i in range(n):
                term = both(term,i if (word >> (n-1-i)) & 1 else neg(i))
            out = nand(neg(out),neg(term))
    return tuple(gates),out


def surjective_affine_and_pairs(points,width):
    anchor = min(points)
    for mask in range(1,1 << width):
        assert any(((x ^ anchor) & mask).bit_count()%2 for x in points)
    for i,j in combinations(range(width),2):
        assert {(((x>>i)&1),((x>>j)&1)) for x in points} == {
            (0,0),(0,1),(1,0),(1,1)}


def exhaustive(n):
    fibers = [set() for _ in range(1 << n)]
    for x in range(1 << (4*n)):
        y = original_decode(n,x)
        free = x >> n
        assert decode(n,x) == y and lift(n,y,free) == x
        fibers[y].add(x)
    for fiber in fibers:
        assert len(fiber) == 1 << (3*n)
        surjective_affine_and_pairs(fiber,4*n)
    for mask in range(1 << (1 << n)):
        F = source(n,mask)
        masked = compile_source(n,F)
        actual = {x for x in range(1 << (4*n)) if evaluate(4*n,masked,x)}
        expected = set().union(*(fiber for y,fiber in enumerate(fibers)
                                if (mask >> y) & 1))
        assert actual == expected and len(actual) == mask.bit_count()*(1 << (3*n))


def median(n):
    # Distinct compact AND presentation; the zero-prefix preimage has its
    # first witness at the all-ones tail with all triple bits zero.
    gates = []
    out = 0
    for i in range(1,n):
        w = n+len(gates)
        gates.extend(((out,i),(w,w)))
        out = w+1
    F = (tuple(gates),out)
    masked = compile_source(n,F)
    result = solve(4*n,masked)
    expected = (1 << n)-1
    assert result['status'] == 'witness' and result['assignment'] == expected
    assert original_decode(n,expected) == expected and evaluate(n,F,expected)
    assert evaluate(4*n,masked,expected)
    assert result['phases'] == 1 and result['fresh_rows'] == result['fresh_clauses'] == 0
    assert result['crossings'] == (1 << n)+3*n-1
    assert result['false_crossings'] == result['crossings']-1
    assert result['forecasts'] >= result['crossings']


if __name__ == '__main__':
    for dimension in range(3):
        exhaustive(dimension)
    for dimension in (2,3):
        median(dimension)
    print('Masked NAND fibers, projections, affine spans and median counts agree.')
