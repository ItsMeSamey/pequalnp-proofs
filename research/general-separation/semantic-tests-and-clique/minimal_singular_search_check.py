"""Sharp characteristic-two minor bound and sorted constrained search, without dependencies."""
from itertools import combinations, permutations, product
from random import Random


class Field:
    def __init__(self, q, modulus):
        self.q = q
        def multiply(a, b):
            value = 0
            while b:
                if b & 1:
                    value ^= a
                a <<= 1
                if a & q:
                    a ^= modulus
                b >>= 1
            return value
        self.mul = [[multiply(a,b) for b in range(q)] for a in range(q)]
        self.inv = [0] + [row.index(1) for row in self.mul[1:]]


def minor(A, chosen, F):
    rows = [[A[i][j] for j in chosen] for i in chosen]
    det = 1
    for j in range(len(rows)):
        k = next((i for i in range(j,len(rows)) if rows[i][j]), None)
        if k is None:
            return 0
        rows[k],rows[j] = rows[j],rows[k]
        det = F.mul[det][rows[j][j]]
        inverse = F.inv[rows[j][j]]
        for i in range(j+1,len(rows)):
            scale = F.mul[rows[i][j]][inverse]
            for col in range(j+1,len(rows)):
                rows[i][col] ^= F.mul[scale][rows[j][col]]
    return det


def schur(A, mandatory, live, F):
    indexes = mandatory + live
    rows = [[A[i][j] for j in indexes] for i in indexes]
    for i in range(len(mandatory)):
        pivot = next((j for j in range(i,len(mandatory)) if rows[j][i]), None)
        if pivot is None:
            return None
        rows[i], rows[pivot] = rows[pivot], rows[i]
        for j in range(i+1,len(rows)):
            scale = F.mul[rows[j][i]][F.inv[rows[i][i]]]
            for k in range(i+1,len(rows)):
                rows[j][k] ^= F.mul[scale][rows[i][k]]
    m = len(mandatory)
    return [row[m:] for row in rows[m:]]


def stream(A, required, excluded, F):
    def visit(chosen, live):
        R = schur(A, chosen, live, F)
        if R is not None and all(minor(R, subset, F)
                for size in range(1,min(F.q,len(live))+1)
                for subset in combinations(range(len(live)), size)):
            return
        if not live:
            yield sum(1 << i for i in chosen)
            return
        yield from visit(chosen, live[1:])
        yield from visit(chosen + live[:1], live[1:])
    # High site first, zero branch first, gives increasing integer masks.
    live = [i for i in reversed(range(len(A))) if not (required | excluded) >> i & 1]
    return visit([i for i in range(len(A)) if required >> i & 1], live)


def check_matrix(A, F, restrictions):
    n = len(A)
    zeros = [s for s in range(1 << n) if not minor(A,[i for i in range(n) if s >> i & 1],F)]
    zero_set = set(zeros)
    for s in zeros:
        if not any(t != s and t & s == t for t in zero_set):
            assert s.bit_count() <= F.q
    for required, excluded in restrictions:
        assert list(stream(A,required,excluded,F)) == [
            s for s in zeros if s & required == required and not s & excluded]


def paths(F):
    q = F.q
    # Every ordered potential list is affine-equivalent to exactly one with prefix
    # (0,1). Scaling conductances by a common constant scales each order-k minor
    # by its kth power. The claimed forest formula has the same homogeneity.
    count = 0
    for tail in permutations(range(2,q)):
        s = (0,1) + tail
        edges = [F.inv[a ^ b] for a,b in zip(s,s[1:])]
        diagonal = [a ^ b for a,b in zip([0]+edges,edges+[0])]
        edge_product = 1
        for c in edges:
            edge_product = F.mul[edge_product][c]
        minors = [1]
        for mask in range(1,1 << q):
            i = mask.bit_length()-1
            previous = mask ^ (1 << i)
            value = F.mul[diagonal[i]][minors[previous]]
            if i and previous >> (i-1) & 1:
                edge = edges[i-1]
                value ^= F.mul[F.mul[edge][edge]][minors[previous ^ (1 << (i-1))]]
            minors.append(value)
        assert minors[-1] == 0
        for mask in range((1 << q)-1):
            roots = [s[i] for i in range(q) if not mask >> i & 1]
            expected = edge_product
            for a,b in zip(roots, roots[1:]):
                expected = F.mul[expected][a ^ b]
            assert expected and minors[mask] == expected
        count += 1
    return count


def main():
    rng = Random(20423)
    F = Field(4,7)
    total = 0
    for n in range(1,4):
        upper = list(combinations(range(n),2)) + [(i,i) for i in range(n)]
        for values in product(range(4),repeat=len(upper)):
            A = [[0]*n for _ in range(n)]
            for (i,j),v in zip(upper,values):
                A[i][j] = A[j][i] = v
            required = rng.randrange(1 << n)
            excluded = rng.randrange(1 << n) & ~required
            check_matrix(A,F,[(0,0),(required,excluded)])
            total += 1
    for n in range(4,8):
        for _ in range(20):
            A = [[0]*n for _ in range(n)]
            for i in range(n):
                for j in range(i+1):
                    A[i][j] = A[j][i] = rng.randrange(4)
            required = rng.randrange(1 << n)
            excluded = rng.randrange(1 << n) & ~required
            check_matrix(A,F,[(0,0),(required,excluded)])
    # Singular mandatory prefix has nonsingular as well as singular extensions.
    assert list(stream([[0,1],[1,0]],1,0,F)) == [1]
    print("GF4 matrices", total, "exhaustive + 80 seeded; normalized path orders",
          [paths(Field(q,mod)) for q,mod in ((2,3),(4,7),(8,11))])


if __name__ == "__main__":
    main()
