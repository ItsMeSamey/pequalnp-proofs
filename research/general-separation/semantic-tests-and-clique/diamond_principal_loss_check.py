"""Check minimal GF(4) support losses on every lane path of a diamond chain."""
from itertools import product
from quaternary_support_check import determinant, omega


def matrices(n, edges, c, a, b):
    H = [[int(i == j and bool(c >> i & 1)) for j in range(n)] for i in range(n)]
    for i, j in edges:
        H[i][j] = H[j][i] = 1
    K = [[H[i][j] ^ (omega if b >> i & b >> j & 1 else 0) for j in range(n)] for i in range(n)]
    U = [[K[i][j] ^ (a >> i & a >> j & 1) for j in range(n)] for i in range(n)]
    return K, U


def check_chain(m):
    # Spine vertices 0..m, private lanes m+1..3m, and the two leaves thereafter.
    n = 3*m+3
    w, end = n-2, n-1
    pairs = [(m+1+2*i, m+2+2*i) for i in range(m)]
    edges = [(u, lane) for i, pair in enumerate(pairs) for lane in pair for u in (i,i+1)]
    edges.extend([(0,w),(m,end)])
    c = (1<<m) | (1<<end)
    a = 1
    b = a ^ (1<<w) ^ c
    K, U = matrices(n,edges,c,a,b)
    adj = [sum(1<<j for j in range(n) if (i,j) in edges or (j,i) in edges) for i in range(n)]
    assert not any((x&a).bit_count()%2 == 1 and (x&b).bit_count()%2 == 0 and
                   all(not (x>>i&1) or (x&adj[i]).bit_count()%2 == (c>>i&1) for i in range(n))
                   for x in range(1<<n))
    cache = {}
    def loss(s):
        if s not in cache:
            I = [i for i in range(n) if s>>i&1]
            before, after = [determinant([[M[i][j] for j in I] for i in I]) for M in (K,U)]
            cache[s] = bool(before) and not after
        return cache[s]
    paths = set()
    for lanes in product(*pairs):
        path = (1<<(m+1))-1 | sum(1<<v for v in lanes)
        assert path not in paths
        paths.add(path)
        assert loss(path)
        sub = (path-1)&path
        while True:
            assert not loss(sub)
            if not sub:break
            sub = (sub-1)&path
    return len(paths),len(cache)


if __name__=='__main__':
    for m in range(1,5):print(m,check_chain(m))
    K,U = matrices(3,[(0,1)],3,1,4)
    losses, gains = [], []
    for s in range(8):
        I = [i for i in range(3) if s>>i&1]
        a,b = [determinant([[M[i][j] for j in I] for i in I]) for M in (K,U)]
        if a and not b:losses.append(s)
        if b and not a:gains.append(s)
    assert 1 in losses and 3 in gains and all(s&1 for s in gains)
    print('3-vertex loss masks',losses,'gain masks',gains)
