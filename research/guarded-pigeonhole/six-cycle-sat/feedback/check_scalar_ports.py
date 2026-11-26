"""Fuse asymmetric scalar bags and twisted alternating bags along named ports."""
from functools import lru_cache
from random import Random

rng = Random(7701)


def bag(names):
    n = len(names)
    M = [[rng.randrange(2) if i != j else 0 for j in range(n)] for i in range(n)]
    C = [[0]*(2*n) for _ in range(2*n)]
    for i in range(n):
        for j in range(n):
            C[2*i][2*j+1] = C[2*j+1][2*i] = M[i][j]
    for i in range(n):
        for _ in range(rng.randrange(5)):
            a = 2*i + rng.randrange(2)
            b = a ^ 1
            C[a] = [x ^ y for x,y in zip(C[a], C[b])]
            for row in C:
                row[a] ^= row[b]
    return names, M, C


def fuse(B, D, port):
    N, M, C = B
    P, H, A = D
    i, j = N.index(port), P.index(port)
    I = [u for u in range(len(N)) if u != i]
    J = [u for u in range(len(P)) if u != j]
    def matrix(S, T, left, right, cross, back):
        return ([[S[u][v] for v in left]+[cross(u,v) for v in right] for u in left]
                + [[back(u,v) for v in left]+[T[u][v] for v in right] for u in right])
    K = matrix(M,H,I,J,lambda u,v:M[u][i]*H[j][v],lambda u,v:H[u][j]*M[i][v])
    def cross(u,v):
        return (C[u][2*i]*A[v][2*j+1]) ^ (C[u][2*i+1]*A[v][2*j])
    E = matrix(C,A,[2*u+b for u in I for b in range(2)],
               [2*v+b for v in J for b in range(2)],cross,lambda u,v:cross(v,u))
    return [N[u] for u in I]+[P[v] for v in J],K,E


def audit(B):
    N,M,C = B
    @lru_cache(None)
    def pf(S):
        if not S:
            return 1
        a,*rest = S
        return sum(C[a][v]*pf(tuple(w for w in rest if w != v)) for v in rest) % 2
    @lru_cache(None)
    def det(rows,cols):
        if not rows:
            return 1
        return sum(M[rows[0]][v]*det(rows[1:],tuple(w for w in cols if w != v))
                   for v in cols) % 2
    for mask in range(1<<len(N)):
        indices = tuple(i for i in range(len(N)) if mask>>i&1)
        assert pf(tuple(2*i+b for i in indices for b in range(2))) == det(indices,indices)
    return 1<<len(N)


if __name__ == '__main__':
    tests = 0
    for case in range(60):
        # Two intermediate composites retain the independent central port z.
        left = fuse(bag(['a','b','x']),bag(['x','z','c']),'x')
        right = fuse(bag(['e','d','y']),bag(['y','z','f']),'y')
        tests += audit(left)+audit(right)+audit(fuse(left,right,'z'))
    print(f'60 three-join trees; {tests} exhaustive whole-pair principal identities')
