"""Deterministic GF(2) affine NAE3 decision and witness for polar rank <= 2.

Bit i of an integer is coordinate i.  A block is (row0, row1, offset)
with a two-bit offset.  solve_nae accepts literals as (variable index, negated).
Run as a script for differential tests. None denotes inconsistency.
"""
from collections import deque
from itertools import product
from random import Random


def dot(a, b):
    return (a & b).bit_count() % 2


def reduce_vector(v, pivots):
    for i in sorted(pivots, reverse=True):
        if v >> i & 1:
            v ^= pivots[i]
    return v


def basis(rows):
    pivots = {}
    for v in rows:
        v = reduce_vector(v, pivots)
        if v:
            pivots[v.bit_length() - 1] = v
    return pivots


def affine_system(n, equations):
    """A point and a kernel basis, or None."""
    pivots = {}
    for v, b in equations:
        while v and v.bit_length()-1 in pivots:
            u, c = pivots[v.bit_length()-1]
            v, b = v ^ u, b ^ c
        if v:
            pivots[v.bit_length()-1] = (v, b)
        elif b:
            return None

    def complete(x, homogeneous):
        for i in sorted(pivots):
            v, b = pivots[i]
            if dot(v, x) ^ (0 if homogeneous else b):
                x ^= 1 << i
        return x

    return complete(0, False), [complete(1 << i, True) for i in range(n) if i not in pivots]


def swap(v):
    even = sum(1 << i for i in range(0, v.bit_length(), 2))
    return ((v & even) << 1) | ((v >> 1) & even)


def representatives(blocks, quotient=()):
    """Augment a common independent set of labeled linear/partition matroids."""
    pivots = basis(quotient)
    raw = [v for a,b,_ in blocks for v in (a,b,a^b)]
    vectors = [reduce_vector(v,pivots) for v in raw]
    chosen = set()
    while True:
        owner = {i//3:i for i in chosen}
        # Tagged linear echelon rows encode fundamental exchange circuits.
        tagged = {}
        for i in sorted(chosen):
            v, tag = vectors[i], 1 << i
            while v and v.bit_length()-1 in tagged:
                u,t = tagged[v.bit_length()-1]
                v,tag = v^u,tag^t
            assert v
            tagged[v.bit_length()-1] = v,tag
        edges = {i:[] for i in range(len(raw))}
        sink = set()
        outside = [i for i in range(len(raw)) if i not in chosen]
        for j in outside:
            v,tag = vectors[j],0
            while v and v.bit_length()-1 in tagged:
                u,t = tagged[v.bit_length()-1]
                v,tag = v^u,tag^t
            if v:
                sink.add(j)
            else:
                for i in chosen:
                    if tag >> i & 1:
                        edges[j].append(i)
        for j in outside:
            if j//3 in owner:
                edges[owner[j//3]].append(j)
        queue = deque(i for i in outside if i//3 not in owner)
        parent = dict.fromkeys(queue)
        while queue:
            i = queue.popleft()
            if i in sink:
                while i is not None:
                    chosen.symmetric_difference_update((i,))
                    i = parent[i]
                break
            for j in edges[i]:
                if j not in parent:
                    parent[j] = i
                    queue.append(j)
        else:
            return sorted(chosen)


def eval_word(rows, x):
    return sum(dot(row,x) << i for i,row in enumerate(rows))


def graph_solution(graph, shift, lam, b):
    n = len(graph)
    ones = (1 << n)-1
    if dot(lam,ones) == b:
        return ones
    marked = [1 ^ ((shift >> i)&1) ^ dot(row,ones) ^ ((row>>i)&1)
              for i,row in enumerate(graph)]
    for i in range(n):
        if lam>>i&1 and not marked[i]:
            return ones ^ (1<<i)
    # Multi-source BFS finds a shortest path from a marked 1 to a marked 0.
    queue = deque(i for i in range(n) if marked[i] and lam>>i&1)
    parent = dict.fromkeys(queue)
    while queue:
        i = queue.popleft()
        if marked[i] and not (lam>>i&1):
            while i is not None:
                ones ^= 1<<i
                i = parent[i]
            return ones
        for j in range(n):
            if graph[i]>>j&1 and j not in parent:
                parent[j] = i
                queue.append(j)
    return None


def solve_blocks(n, blocks):
    def flat(bs):
        return [r for a,b,_ in bs for r in (a,b)]

    def columns(rows, width):
        return [eval_word(rows,1<<j) for j in range(width)]

    def rep_eq(bs, reps):
        for j in reps:
            a,b,p = bs[j//3]
            mask = (1,2,3)[j%3]
            yield (a,b,a^b)[j%3], 1^dot(mask,p)

    t = len(blocks)
    rows = flat(blocks)
    image = list(basis(columns(rows,n)).values())
    gram = [eval_word(image,swap(v)) for v in image]
    rank = 2*(t-len(image))+len(basis(gram))
    if rank > 2:
        raise ValueError("polar rank exceeds two")
    reps = representatives(blocks)
    if len(reps) == t:
        return affine_system(n,rep_eq(blocks,reps))[0]
    assert len(reps) == t-1
    I = list(range(t))
    for i in range(t):
        trial = [j for j in I if j != i]
        if len(representatives([blocks[j] for j in trial])) < len(trial):
            I = trial
    inner = [blocks[i] for i in I]
    selected = set(I)
    outer = [g for i,g in enumerate(blocks) if i not in selected]
    m = len(I)
    local_rows = flat(inner)
    L = list(basis(columns(local_rows,n)).values())
    ortho = affine_system(2*m,[(swap(v),0) for v in L])[1]
    pivots = basis(L)
    extension = next(v for v in ortho if reduce_vector(v,pivots))
    L0 = L+[extension]
    coord = columns(L0,2*m)
    chart = [(coord[2*i],coord[2*i+1],0) for i in range(m)]
    tests = representatives(chart)
    assert len(tests)==m
    masks = [(1,2,3)[j%3] for j in tests]
    dual = [2 if msk==1 else 1 for msk in masks]
    def transform(w, tests):
        return sum(dot(w>>(2*i),msk)<<i for i,msk in enumerate(tests))
    X = [transform(w,masks) for w in L0]
    Y = [transform(w,dual) for w in L0]
    offset = sum(p<<(2*i) for i,(_,_,p) in enumerate(inner))
    px,py = transform(offset,masks),transform(offset,dual)
    graph = [affine_system(m,[(x,(y>>i)&1) for x,y in zip(X,Y)])[0] for i in range(m)]
    shift = py ^ eval_word(graph,px)
    lam = affine_system(m,[(x,int(i==m-1)) for i,x in enumerate(X)])[0]
    x = graph_solution(graph,shift,lam,dot(lam,px))
    if x is None:
        return None
    y = eval_word(graph,x)^shift
    equations = []
    for i,(a,b,p) in enumerate(inner):
        for test,word in ((masks[i],x),(dual[i],y)):
            equations.append(((a,b,a^b)[test-1],((word>>i)&1)^dot(test,p)))
    outside = representatives(outer,local_rows)
    assert len(outside)==len(outer)
    equations.extend(rep_eq(outer,outside))
    sol = affine_system(n,equations)[0]
    assert all(eval_word((a,b),sol)^p for a,b,p in blocks)
    return sol


def solve_nae(n, gates, equations=()):
    space = affine_system(n,equations)
    if space is None:
        return None
    point, kernel = space
    blocks=[]
    for (i,p),(j,q),(k,r) in gates:
        a,b = (1<<i)^(1<<j),(1<<i)^(1<<k)
        blocks.append((eval_word(kernel,a),eval_word(kernel,b),
                       (p^q^dot(a,point)) | ((p^r^dot(b,point))<<1)))
    seed = solve_blocks(len(kernel),blocks)
    if seed is None:
        return None
    for i,v in enumerate(kernel):
        if seed>>i&1:
            point ^= v
    return point


def self_test():
    rng=Random(4921)
    passed=0
    unsat=0
    def check(n,bs):
        nonlocal passed,unsat
        try:
            actual=solve_blocks(n,bs)
        except ValueError:
            return
        valid=[w for w in range(1<<n) if all(eval_word((a,b),w)^p for a,b,p in bs)]
        assert (actual in valid) if valid else actual is None
        passed+=1
        unsat+=not valid
    for n in range(3):
        opts=list(product(range(1<<n),range(1<<n),range(4)))
        for t in range(3):
            for bs in product(opts,repeat=t):
                check(n,bs)
    for _ in range(2000):
        n,t=rng.randrange(1,7),rng.randrange(1,6)
        check(n,[(rng.randrange(1<<n),rng.randrange(1<<n),rng.randrange(4)) for _ in range(t)])
    for _ in range(500):
        # Produce isotropic codimension-one slices explicitly.
        m=rng.randrange(2,8)
        G=[0]*m
        for i in range(m):
            for j in range(i,m):
                if rng.randrange(2):
                    G[i]|=1<<j
                    G[j]|=1<<i
        lam=rng.randrange(1,1<<m)
        K=affine_system(m,[(lam,0)])[1]
        check(m-1,[(eval_word(K,1<<i),eval_word(K,G[i]),rng.randrange(4)) for i in range(m)])
    nae_cases=0
    for _ in range(1000):
        n=rng.randrange(1,7)
        gates=[[(rng.randrange(n),rng.randrange(2)) for _ in range(3)] for _ in range(rng.randrange(5))]
        eq=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))]
        try:
            actual=solve_nae(n,gates,eq)
        except ValueError:
            continue
        valid=[x for x in range(1<<n) if all(dot(x,v)==b for v,b in eq) and
               all(len({((x>>i)&1)^p for i,p in gate})==2 for gate in gates)]
        assert (actual in valid) if valid else actual is None
        nae_cases+=1
    print(f"{passed} block cases ({unsat} UNSAT), {nae_cases} signed NAE cases passed")


if __name__ == "__main__":
    self_test()
