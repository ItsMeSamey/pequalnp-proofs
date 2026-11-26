"""Finite independent reconstruction of the affine rank-two NAE solver."""
from itertools import product
from collections import deque


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {u ^ v for u in values}
    return values


def basis(space):
    result = []
    values = {0}
    for v in sorted(space):
        if v not in values:
            result.append(v)
            values |= {u ^ v for u in values}
    return result


def parity(v):
    return v.bit_count() % 2


def swap(v, t):
    return sum((((v >> (2*i)) & 1) << (2*i+1)) |
               (((v >> (2*i+1)) & 1) << (2*i)) for i in range(t))


def all_subspaces(t):
    seen = {frozenset({0})}
    current = list(seen)
    while current:
        space = current.pop()
        yield space
        for v in range(1, 1 << (2*t)):
            if v not in space:
                new = space | {w ^ v for w in space}
                if new not in seen:
                    seen.add(new)
                    current.append(new)


def packed(v, indexes):
    return sum(((v >> (2*i)) & 3) << (2*j) for j, i in enumerate(indexes))


def transversal(indexes, space, initial=()):
    b = basis(space)
    def row(i, key):
        return sum(parity((x >> (2*i)) & key) << j for j,x in enumerate(b))
    base_rows = [row(i, key) for i, key in initial]
    base_dim = len(basis(span(base_rows)))
    for keys in product((1,2,3), repeat=len(indexes)):
        rows = [row(i, k) for i,k in zip(indexes,keys)]
        if len(span(base_rows + rows)) == 1 << (base_dim + len(rows)):
            return list(zip(indexes,keys))
    raise AssertionError("no Rado representatives")


def all_nonzero(w, t):
    return all((w >> (2*i)) & 3 for i in range(t))


def graph_witness(g, offset, lam, rhs):
    t = len(g)
    ones = (1 << t) - 1
    if parity(ones & lam) == rhs:
        return ones
    marked = sum((1 ^ ((offset>>i)&1) ^ parity(row) ^ ((row>>i)&1))<<i
                 for i, row in enumerate(g))
    good = lam & ~marked
    if good:
        return ones ^ (good & -good)
    # Find a shortest route from any marked 1 to a marked 0.
    starts = [i for i in range(t) if ((lam >> i)&1)]
    queue = deque(starts)
    predecessor = {i:None for i in starts}
    while queue:
        i = queue.popleft()
        if ((marked >> i)&1) and not ((lam >> i)&1):
            mask = 0
            while i is not None:
                mask |= 1 << i
                i = predecessor[i]
            return ones ^ mask
        for j in range(t):
            if ((g[i] >> j)&1) and j not in predecessor:
                predecessor[j] = i
                queue.append(j)
    return None


def prepare(space, t):
    # Compute polar rank directly on the ordinary annihilator.
    fourier = [v for v in range(1 << (2*t)) if all(not parity(v & w) for w in space)]
    fb = basis(fourier)
    gram = [sum(parity(swap(u,t)&v)<<i for i,v in enumerate(fb)) for u in fb]
    rank = len(basis(span(gram)))
    if rank > 2:
        return None
    all_indices = tuple(range(t))
    deficits = []
    for mask in range(1 << t):
        ix = tuple(i for i in all_indices if mask>>i&1)
        restriction = {packed(v,ix) for v in space}
        deficits.append((len(ix)-len(basis(restriction)), -len(ix), ix, restriction))
    delta, _, ix, restricted = max(deficits,key=lambda d:d[:2])
    outside = tuple(i for i in all_indices if i not in ix)
    fixed = [(i,k) for i in ix for k in (1,2)]
    partial = transversal(outside, space, fixed)
    def extend(p, word):
        return next(v^p for v in space if packed(v^p, ix)==word and
                    all(parity(((v^p) >> (2*i))&k) for i,k in partial))
    if delta == 0:
        assert ix == ()
        return rank, lambda p: extend(p,0)
    assert delta == 1 and rank==2
    k = len(ix)
    ext = next(v for v in range(1<<(2*k)) if v not in restricted and
               all(not parity(swap(v,k)&w) for w in restricted))
    lag = span(list(restricted)+[ext])
    first = [key for _,key in transversal(range(k),lag)]
    second = [next(i for i in (1,2,3) if i!=f) for f in first]
    def coords(w, tests):
        return sum(parity((w>>(2*i)) & key) << i for i,key in enumerate(tests))
    linear = {coords(w,first):coords(w,second) for w in lag}
    cols = [linear[1<<j] for j in range(k)]
    rows = [sum(((col>>i)&1)<<j for j,col in enumerate(cols)) for i in range(k)]
    assert rows==cols
    lam = next(v for v in range(1,1<<k) if all(not parity(v & coords(w,first)) for w in restricted))
    def solve(p):
        off = packed(p,ix)
        x0,y0 = coords(off,first),coords(off,second)
        x = graph_witness(rows,y0 ^ linear[x0],lam,parity(lam & x0))
        if x is None:
            return None
        word = next(w ^ off for w in lag if coords(w^off,first)==x)
        return extend(p,word)
    return rank,solve


def main():
    counts = {0:0, 2:0}
    for t in (1,2,3):
        for space in all_subspaces(t):
            prep = prepare(space,t)
            if prep is None:
                continue
            rank,solve = prep
            todo = set(range(1<<(2*t)))
            while todo:
                p = min(todo)
                coset = {v^p for v in space}
                todo -= coset
                answer = solve(p)
                possible = any(all_nonzero(v,t) for v in coset)
                assert possible == (answer is not None), (t,space,p,answer)
                if possible:
                    assert answer in coset and all_nonzero(answer,t)
                counts[rank]+=1
    print("All affine cosets on 1–3 blocks passed; ranks and counts",counts)

if __name__ == '__main__':
    main()
