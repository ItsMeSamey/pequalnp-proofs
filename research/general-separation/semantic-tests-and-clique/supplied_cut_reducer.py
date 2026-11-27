"""One supplied low-rank cut; reduce_cut returns new rows, pins and a mask lift."""
from collections import deque
from functools import reduce
from itertools import combinations, product
from operator import xor
from random import Random


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low


def path(A, starts, ends, neutral, direct=True):
    parent = {i: None for i in starts}
    queue = deque(parent)
    while queue:
        i = queue.popleft()
        for j in bits(A[i]):
            if j in parent:
                continue
            if j in ends and (direct or i not in starts):
                w = 1 << j
                while i is not None:
                    w |= 1 << i
                    i = parent[i]
                return w
            if j in neutral:
                parent[j] = i
                queue.append(j)
    return None


def even(A, labels, s):
    if s == 0:
        return 0
    if s in labels:
        return 1 << labels.index(s)
    a,b = [v for v in range(1,4) if v != s]
    E,F,Z = ({i for i,c in enumerate(labels) if c == v} for v in (a,b,0))
    for i,j in product(E,F):
        if not A[i] >> j & 1:
            return (1 << i) | (1 << j)
    return path(A,E,F,Z,False)


def table(A, labels, k, pin):
    result = {}
    for t,s in product(range(1 << k),repeat=2):
        if (t&s).bit_count()%2:
            continue
        if t == 0:
            colors = labels if pin is None else [v | (int(i == pin)<<1) for i,v in enumerate(labels)]
            w = even(A,colors,s if pin is None else s|2)
        elif pin is not None:
            odd = {i for i,v in enumerate(labels) if v}
            w = path(A,{pin},odd-{pin},set(range(len(A)))-odd) if pin in odd else 1 << pin
        elif not s:
            w = 0
        elif s in labels:
            w = 1 << labels.index(s)
        else:
            a,b = [v for v in range(1,4) if v != s]
            E,F,Z = ({i for i,c in enumerate(labels) if c == v} for v in (a,b,0))
            w = path(A,E,F,Z)
        if w is not None:
            assert reduce(xor,(labels[i] for i in bits(w)),0) == s
            assert all(((A[i]&w).bit_count() ^ (labels[i]&t).bit_count())%2 == 0 for i in bits(w))
            result[t,s] = w
    return result


def brute(A,labels,k,pin):
    result = set()
    for w in range(1 << len(A)):
        if pin is not None and not w >> pin & 1:
            continue
        s = reduce(xor,(labels[i] for i in bits(w)),0)
        for t in range(1 << k):
            if all(((A[i]&w).bit_count() ^ (labels[i]&t).bit_count())%2 == 0 for i in bits(w)):
                result.add((t,s))
    return result


def graphs(n):
    pairs = list(combinations(range(n),2))
    for edges in range(1 << len(pairs)):
        A = [0]*n
        for i in bits(edges):
            a,b = pairs[i]
            A[a] |= 1 << b
            A[b] |= 1 << a
        yield A


def induced(A, vertices):
    return [sum(((A[i] >> j)&1) << k for k,j in enumerate(vertices)) for i in vertices]


def reduce_cut(A, side, pins):
    X = sorted(side)
    Y = sorted(set(range(len(A))) - set(X))
    inside = set(pins) & set(X)
    if len(inside) > 1:
        raise ValueError("side contains multiple pins")
    p = X.index(next(iter(inside))) if inside else None
    limit = 2 if p is None else 1
    vectors = [0]
    colors = []
    for i in X:
        v = sum(((A[i] >> j)&1) << k for k,j in enumerate(Y))
        if v not in vectors:
            if len(vectors) == 1 << limit:
                raise ValueError("supplied cut rank too high")
            vectors += [u ^ v for u in vectors]
        colors.append(vectors.index(v))
    k = len(vectors).bit_length()-1
    reps = table(induced(A,X),colors,k,p)
    for n in range(int(p is not None),4):
        for labels in product(range(1 << k),repeat=n):
            if p is not None and labels[0] != colors[p]:
                continue
            for internal in graphs(n):
                if brute(internal,labels,k,0 if p is not None else None) != set(reps):
                    continue
                offset = len(Y)
                B = induced(A,Y)
                for j,c in enumerate(labels):
                    B.append(vectors[c] | (internal[j] << offset))
                    for i in bits(vectors[c]):
                        B[i] |= 1 << (offset+j)
                Q = [offset if i in inside else Y.index(i) for i in pins]
                def lift(mask):
                    y = mask & ((1 << offset)-1)
                    t = sum(((vectors[1 << j]&y).bit_count()%2) << j for j in range(k))
                    s = reduce(xor,(labels[i] for i in bits(mask >> offset)),0)
                    return sum(1 << X[i] for i in bits(reps[t,s])) | sum(1 << Y[i] for i in bits(y))
                return B,Q,lift
    raise AssertionError("no gadget")


def valid(A,pins):
    return {w for w in range(1 << len(A)) if all(w >> i & 1 for i in pins)
            and all(not ((A[i]&w).bit_count()%2) for i in bits(w))}


def check():
    count = 0
    for n in range(4):
        for A in graphs(n):
            for k in range(3):
                for labels in product(range(1 << k),repeat=n):
                    for pin in [None] + (list(range(n)) if k <= 1 else []):
                        assert set(table(A,labels,k,pin)) == brute(A,labels,k,pin)
                        count += 1
    rng = Random(181)
    for case in range(100):
        A = [0]*8
        pin = case%2
        colors = [rng.randrange(2 if pin else 4) for _ in A]
        for i,j in combinations(range(8),2):
            edge = (colors[i]&colors[j]).bit_count()%2 if i < 4 <= j else rng.randrange(2)
            if edge:
                A[i] |= 1 << j
                A[j] |= 1 << i
        pins = [0,5,7] if pin else [4,5,7]
        B,Q,lift = reduce_cut(A,range(4),pins)
        original = valid(A,pins)
        lifted = {lift(w) for w in valid(B,Q)}
        assert lifted <= original
        assert {w >> 4 for w in original} == {w >> 4 for w in lifted}
    print(count,"side tables; 100 full graph witness/exterior comparisons")


if __name__ == "__main__":
    check()
