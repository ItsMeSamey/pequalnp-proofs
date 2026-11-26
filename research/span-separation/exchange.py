from collections import deque


def eliminate(columns):
    pivots = {}
    for index, col in enumerate(columns):
        coeff = 1 << index
        while col:
            key = col.bit_length()-1
            if key not in pivots:
                pivots[key] = (col, coeff)
                break
            value, rep = pivots[key]
            col ^= value
            coeff ^= rep
    return pivots


def represent(pivots, target):
    coeff = 0
    while target:
        key = target.bit_length()-1
        if key not in pivots:
            return None
        value, rep = pivots[key]
        target ^= value
        coeff ^= rep
    return coeff


def quotient(col, w):
    bit = 1 << (w.bit_length()-1)
    return col ^ w if col & bit else col


def solve(columns, u, w):
    piv = eliminate(columns)
    first = represent(piv, u)
    if first is None or w == 0:
        return None
    if represent(piv, w) is None or u == 0:
        return [i for i in range(len(columns)) if first >> i & 1]
    if u == w:
        return None
    # Pick a basis in the quotient by w, using original column indices.
    quot = [quotient(a, w) for a in columns]
    basis = sorted(rep.bit_length()-1 for _,rep in eliminate(quot).values())
    base_cols = [columns[j] for j in basis]
    b = len(basis)
    piv = eliminate(base_cols + [w])
    sig = represent(piv, u)
    if not sig >> b:
        return basis
    s = sig ^ (1 << b)
    pos = set(basis)
    # Rows have identifiers 0..b-1 and each nonbasis column j has node b+j.
    graph = [[] for _ in range(b+len(columns))]
    ends = set()
    for j,a in enumerate(columns):
        if j in pos:
            continue
        coord = represent(piv, a)
        if coord >> b:
            ends.add(b+j)
        for i in range(b):
            if coord >> i & 1:
                graph[i].append(b+j)
                graph[b+j].append(i)
    parent = {i:None for i in range(b) if s >> i & 1}
    queue = deque(parent)
    while queue:
        node = queue.popleft()
        if node in ends:
            nodes = set()
            while node is not None:
                nodes.add(node)
                node = parent[node]
            return ([j for i,j in enumerate(basis) if i not in nodes] +
                    [v-b for v in nodes if v >= b])
        for nxt in graph[node]:
            if nxt not in parent:
                parent[nxt] = node
                queue.append(nxt)
    return None


def test():
    from itertools import combinations
    from random import Random
    case = 0
    def check(a,u,w):
        nonlocal case
        want = False
        for mask in range(1<<len(a)):
            b = eliminate([x for i,x in enumerate(a) if mask >> i & 1])
            if represent(b,u) is not None and represent(b,w) is None:
                want = True
                break
        got = solve(a,u,w)
        assert want == (got is not None), (a,u,w,want,got)
        if got is not None:
            b = eliminate([a[i] for i in got])
            assert represent(b,u) is not None and represent(b,w) is None
        case += 1
    for n in range(8):
        for a in combinations(range(1,8),n):
            for u in range(8):
                for w in range(8):
                    check(a,u,w)
    rng = Random(379)
    for _ in range(1200):
        n = rng.randrange(10)
        a = [rng.randrange(32) for _ in range(n)]
        check(a,rng.randrange(32),rng.randrange(32))
    print('passed',case)

if __name__ == '__main__':
    test()
