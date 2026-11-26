"""Compare signed grove evaluations to a literal sum over disjoint tree decompositions."""
from itertools import combinations, permutations, product
from random import Random

P = 101


def determinant(matrix):
    value = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j] % P), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            value = -value
        value = value * matrix[j][j] % P
        inv = pow(matrix[j][j], -1, P)
        for i in range(j + 1, len(matrix)):
            factor = matrix[i][j] * inv % P
            if factor:
                for k in range(j + 1, len(matrix)):
                    matrix[i][k] = (matrix[i][k] - factor * matrix[j][k]) % P
    return value % P


def tree_weight(edges, vertices):
    if len(vertices) == 1:
        return 1
    mapping = {v: i for i, v in enumerate(sorted(vertices))}
    last = len(mapping) - 1
    mat = [[0] * last for _ in range(last)]
    for u, v, w in edges:
        if u not in mapping or v not in mapping:
            continue
        a, b = mapping[u], mapping[v]
        if a < last:
            mat[a][a] += w
        if b < last:
            mat[b][b] += w
        if max(a, b) < last:
            mat[a][b] -= w
            mat[b][a] -= w
    return determinant(mat)


def put_star(edges, ports, center, x):
    g = [x, 1-x, 1, -1]
    for i, a in enumerate(ports):
        edges.append((a, center, g[i]))
        for j in range(i):
            edges.append((a, ports[j], -g[i] * g[j]))


def literal_grove(x):
    n = len(x)
    nverts = 2*n+2+n*n
    edges = []
    for i in range(n):
        for j in range(n):
            put_star(edges, [i, i+1, n+1+j, n+2+j], 2*n+2+i*n+j, x[i][j])
    red = {0,n}
    blue = {n+1,2*n+1}
    all_v = set(range(nverts))
    free = sorted(all_v-red-blue)
    result = 0
    for mask in range(1 << len(free)):
        first = red | {v for k, v in enumerate(free) if mask >> k & 1}
        result += tree_weight(edges, first) * tree_weight(edges, all_v-first)
    return result % P


def is_tree(n, edges):
    group = list(range(n))
    for u,v in edges:
        a,b = group[u],group[v]
        if a == b:
            return False
        group = [a if g==b else g for g in group]
    return len(set(group)) == 1


def amplitude(perm):
    n = len(perm)
    by_col = sorted(range(n), key=perm.__getitem__)
    edges = list(zip(range(n-1),range(1,n))) + list(zip(by_col,by_col[1:]))
    count = 0
    for part in combinations(range(len(edges)),n-1):
        if is_tree(n,[edges[i] for i in part]) and is_tree(n,[e for i,e in enumerate(edges) if i not in part]):
            count += 1
    return count


def predicted(x):
    result = 0
    for perm in permutations(range(len(x))):
        value = amplitude(perm)
        for i,j in enumerate(perm):
            value = value * x[i][j] * (1-x[i][j]) % P
        result += value
    return result % P


if __name__ == '__main__':
    rng = Random(4139)
    for n,cases in [(1,12),(2,12),(3,1)]:
        for _ in range(cases):
            x = [[rng.randrange(P) for j in range(n)] for i in range(n)]
            assert literal_grove(x) == predicted(x)
        print(f'N={n}: {cases} complete signed weight checks modulo {P}')
    values = {p:amplitude(p) for p in permutations(range(4))}
    assert sorted(values.values()) == [8]*22+[12]*2
    print('N=4 complementary trees:',{p:c for p,c in values.items() if c!=8})
