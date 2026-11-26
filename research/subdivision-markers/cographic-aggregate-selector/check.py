from itertools import combinations, product
from random import Random
from solve import apply, charges, score, solve, sparse, tree_coloring


def spanning(n, edges):
    """Return a spanning tree of the supplied edges or None."""
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    tree = []
    for u, v in edges:
        x, y = find(u), find(v)
        if x != y:
            parent[x] = y
            tree.append((u, v))
    return tree if len(tree) == n-1 else None


def tiny_pin_tree(n, edges, pins):
    if len(pins) == n:
        return spanning(n, [(u, v) for u, v in edges if pins[u] != pins[v]])
    zero = [(0, 0)] * n
    for test in combinations(edges, n-1):
        tree = spanning(n, test)
        if tree is not None and tree_coloring(n, tree, zero, pins) is not None:
            return tree
    return None


def brute_scores(n, edges, tags):
    result = set()
    for assignment in product(range(4), repeat=n-1):
        colors = (0,) + assignment
        vals = [colors[a] ^ colors[b] for a, b in edges]
        if spanning(n, [e for e, v in zip(edges, vals) if v]) is not None:
            result.add(score(tags, vals))
    return result


def all_masks(cols):
    basis = {0}
    for c in cols:
        basis |= {v ^ c for v in basis}
    return basis


def brute_physical(n, edges, tags, k):
    m = len(edges)
    masks = all_masks([(1 << u) ^ (1 << v) for u, v in edges])
    assert len(masks) == 1 << (n-1)
    # Build a binary D whose rows comprise all fundamental graph cycles.
    tree = spanning(n, edges)
    rows = []
    for e in set(edges) - set(tree):
        for mask in range(1 << len(tree)):
            demand = (1 << e[0]) ^ (1 << e[1])
            support = 1 << edges.index(e)
            for i,(u,v) in enumerate(tree):
                if mask >> i & 1:
                    demand ^= (1 << u) ^ (1 << v)
                    support |= 1 << edges.index((u,v))
            if demand == 0:
                rows.append(support)
                break
    D = [sum(((row >> j)&1) << i for i,row in enumerate(rows)) for j in range(m)]
    h = len(rows)
    shift = m + 2*h
    ordinary = []
    for i in range(m):
        for color in (1,2,3):
            ordinary.append((1<<i) | ((D[i] if color&1 else 0)<<m)
                            | ((D[i] if color&2 else 0)<<(m+h))
                            | (apply(tags[i],color)<<shift))
    aggregates = [((1<<m)-1) | t<<shift for t in range(1<<k)]
    accepted = set()
    # Enumerate all contraction spans. Different masks with the same span are equivalent.
    spans = {frozenset((0,))}
    for col in ordinary:
        spans |= {span | {x^col for x in span} for span in spans}
    for span in spans:
        if any(t<<shift in span for t in range(1,1<<k)):
            continue
        accepted.update(t for t,r in enumerate(aggregates) if r in span)
    return accepted, 1 << len(ordinary)


def check_small():
    rng = Random(811)
    checks = witnesses = physical = 0
    for i in range(32):
        n = rng.choice((2,3,4,5))
        edges = [(j, rng.randrange(j)) for j in range(1,n)]
        edges = [tuple(sorted(e)) for e in edges]
        possible = [e for e in combinations(range(n),2) if e not in edges]
        edges += [e for e in possible if rng.random() < .4]
        k = i%4
        tags = [(rng.randrange(1<<k), rng.randrange(1<<k)) for e in edges]
        expected = brute_scores(n, edges, tags)
        if len(edges) <= 3:
            actual, masks = brute_physical(n, edges, tags,k)
            assert actual == expected
            physical += masks
        for target in range(1<<k):
            result = solve(n, edges, tags,k,target,tiny_pin_tree)
            assert (result is not None) == (target in expected)
            if result is not None:
                colors, tree = result
                assert all(colors[u] != colors[v] for u,v in tree)
                assert score(tags, [colors[u]^colors[v] for u,v in edges]) == target
                witnesses += 1
            checks += 1
    return checks,witnesses,physical


def dense_control():
    # Two rare pin vertices, two dense independent checksum directions.
    n,k=256,3
    H = []
    for v in range(n):
        a = (1 if v < 2 else 0) | (2 if v%4 < 2 else 0)
        b = 4 if v%8 < 4 else 0
        H.append((a,b))
    edges=[(i,i+1) for i in range(n-1)]
    prefix=[0,0]
    tags=[]
    for a,b in H[:-1]:
        prefix[0] ^= a
        prefix[1] ^= b
        tags.append(tuple(prefix))
    assert tuple(H) == charges(n,edges,tags)
    U,W = sparse(H,k)
    assert U == [0,1] and W == {0,1}
    def path_oracle(n, edges, pins):
        return edges if tree_coloring(n,edges,[(0,0)]*n,pins) is not None else None
    for t in range(1<<k):
        colors, tree = solve(n,edges,tags,k,t,path_oracle)
        assert score(H,colors)==t
    return len(U),len(W),1<<k


if __name__ == '__main__':
    print('Small targets, witnesses, contraction masks',check_small())
    print('Dense path with pin vertices, sparse characters, accepted scores',dense_control())
    K5=list(combinations(range(5),2))
    assert brute_scores(5,K5,[(1,2)]*10) == {0}
    assert not any(all(c[u]!=c[v] for u,v in K5) for c in product(range(4),repeat=5))
    star=[(0,i) for i in range(1,5)]
    assert tiny_pin_tree(5,star,{i:i-1 for i in range(1,5)}) is None
    assert tiny_pin_tree(5,star,dict.fromkeys(range(1,5),0)) is not None
    print('Eulerian K5 and star precoloring controls pass')
