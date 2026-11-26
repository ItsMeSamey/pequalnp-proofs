"""Verify the sparse-promise formula bound on prime-order planes."""
from fractions import Fraction
from itertools import product


def rank(matrix):
    rows = [[Fraction(x) for x in row] for row in matrix]
    count = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(count, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[count], rows[pivot] = rows[pivot], rows[count]
        for i in range(count + 1, len(rows)):
            factor = rows[i][col] / rows[count][col]
            rows[i] = [x - factor * y for x, y in zip(rows[i], rows[count])]
        count += 1
    return count


def plane(q):
    triples = [(a,b,1) for a,b in product(range(q), repeat=2)]
    triples += [(a,1,0) for a in range(q)] + [(1,0,0)]
    n = len(triples)
    return n, [(i,n+j) for i,p in enumerate(triples) for j,l in enumerate(triples)
               if sum(x*y for x,y in zip(p,l)) % q == 0]


def join(op, nodes):
    tree = nodes[0]
    for node in nodes[1:]:
        tree = op, tree, node
    return tree


def gate_values(tree, selected, path=(), out=None):
    if out is None:
        out = {}
    if isinstance(tree, int):
        out[path] = tree in selected
    else:
        op,a,b = tree
        gate_values(a, selected, path+(0,), out)
        gate_values(b, selected, path+(1,), out)
        left, right = out[path+(0,)], out[path+(1,)]
        out[path] = (left or right) if op == 'or' else (left and right)
    return out


def visit(tree, pos, neg):
    path = ()
    while not isinstance(tree, int):
        op,a,b = tree
        take_left = pos[path+(0,)] if op == 'or' else not neg[path+(0,)]
        step = 0 if take_left else 1
        path += (step,)
        tree = a if take_left else b
    return tree, path


def test_plane(q):
    n, edges = plane(q)
    neighbors = [set() for _ in range(2*n)]
    for p,l in edges:
        neighbors[p].add(l)
        neighbors[l].add(p)
    masks = [(neighbors[p] | neighbors[l]) - {p,l} for p,l in edges]
    for mask in masks:
        assert sum(i>=n for i in mask) == q
        assert all(not ({p,l} <= mask) for p,l in edges)
    for centers in (range(n),range(n,2*n)):
        tree = join('or', [('and',c,join('or',sorted(neighbors[c]))) for c in centers])
        pos = [gate_values(tree,set(e)) for e in edges]
        neg = [gate_values(tree,s) for s in masks]
        assert all(row[()] for row in pos) and not any(row[()] for row in neg)
        by_path = {}
        for i,e in enumerate(edges):
            for j,f in enumerate(edges):
                v,path = visit(tree,pos[i],neg[j])
                assert v in e and v not in masks[j]
                if i!=j and set(e)&set(f):
                    assert {v} == set(e)&set(f)
                by_path.setdefault(path, set()).add((i,j))
        assert len(by_path) == n*(q+2)
        for pairs in by_path.values():
            assert len(pairs)==len({i for i,j in pairs})*len({j for i,j in pairs})


if __name__ == '__main__':
    orientations = 0
    for d in range(2,9):
        for zeros in product((False,True), repeat=d):
            matrix = [[int(i!=j or not zeros[i]) for j in range(d)] for i in range(d)]
            assert rank(matrix) == sum(zeros) + (sum(zeros)<d)
            orientations += 1
    for q in (2,3,5):
        test_plane(q)
    print(f'{orientations} local orientations and six full formula traversals passed')
