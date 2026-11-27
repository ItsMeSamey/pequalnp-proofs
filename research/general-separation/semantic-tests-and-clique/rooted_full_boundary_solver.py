"""Constructive linking for a supplied pin-free three-dimensional boundary.

link(rows,pins,side,h=2,representatives=None) returns a status and a physical
witness mask, a separating physical cut mask, or a reason the premise declined.
Masks and witness representatives use original vertex indexes; boundary colors
use the first independent cross rows in increasing side-index order.
"""
from itertools import combinations, product
from supplied_cut_reducer import bits


def mask(vertices):
    return sum(1 << i for i in vertices)


def dot(x,y):
    return (x & y).bit_count() % 2


def image(A,x):
    return sum(dot(row,x) << i for i,row in enumerate(A))


def span(rows):
    values = [0]
    for row in rows:
        if row not in values:
            values += [v ^ row for v in values]
    return values


def separator(A,live,inside,outside):
    """Find a shore containing inside and disjoint from outside, of rank <=2."""
    for k in range(3):
        for I in combinations(bits(live & ~outside),k):
            left = inside | mask(I)
            for J in combinations(bits(live & ~left),k):
                right = mask(J)
                pred = {0:0}
                for i in I:
                    pred.update({p ^ (A[i]&right): r ^ A[i] for p,r in pred.items()})
                if len(pred) != 1 << k:
                    continue
                bad = {i:(A[i] ^ pred[A[i]&right]) & live for i in bits(live)}
                removed = right | outside
                queue = list(bits(removed))
                for w in queue:
                    for i in bits(live & ~removed):
                        if bad[i] >> w & 1:
                            removed |= 1 << i
                            queue.append(i)
                if not removed & left:
                    return live & ~removed
    return None


def edge_pivot(A,i,j):
    assert A[i] >> j & 1
    B = A[:]
    ab = (1 << i) | (1 << j)
    for v in range(len(A)):
        if ab >> v & 1:
            continue
        left,right = (A[v] >> i)&1,(A[v] >> j)&1
        row = A[v]
        if left:
            row ^= A[j]
        if right:
            row ^= A[i]
        B[v] = (row & ~ab) | (left << j) | (right << i)
    B[i] = (A[j] & ~ab) | (1 << j)
    B[j] = (A[i] & ~ab) | (1 << i)
    return B


def link(A,pins,side,h=2,representatives=None):
    n = len(A)
    X,P = mask(side),mask(pins)
    full = (1 << n)-1
    W = full ^ X
    if X & P or P.bit_count() != 3:
        raise ValueError("need three distinct pins disjoint from supplied side")
    cross = [0]
    for i in bits(X):
        row = A[i]&W
        if row not in cross:
            if len(cross) == 8:
                return {"status":"declined", "reason":"rank above three"}
            cross += [u ^ row for u in cross]
    if len(cross) != 8:
        return {"status":"declined","reason":"rank below three"}
    labels = {i:cross.index(A[i]&W) for i in bits(X)}
    reps = {}
    def record(w):
        s = 0
        for i in bits(w):
            s ^= labels[i]
        for t in range(8):
            if all(dot(A[i],w) == dot(labels[i],t) for i in bits(w)):
                reps.setdefault((s,t),w)
    if representatives is not None:
        for w in representatives.values():
            if type(w) is not int or w < 0 or w & ~X:
                raise ValueError("representative outside side")
            record(w)
    for count in range(min(h,X.bit_count())+1):
        if len(reps) == 36:
            break
        for selected in combinations(bits(X),count):
            record(mask(selected))
            if len(reps) == 36:
                break
    if len(reps) != 36:
        return {"status":"declined","reason":"full table unverified","states":len(reps)}
    Q = 7 << n
    B = [row & W if W >> i & 1 else 0 for i,row in enumerate(A)] + [0,0,0]
    for j in range(3):
        row = cross[1 << j]
        B[n+j] = row
        for i in bits(row):
            B[i] |= 1 << (n+j)
    live = W | Q
    shore = separator(B,live,P,Q)
    if shore is not None:
        cut = full ^ shore
        assert not P & cut and X & cut == X
        assert len(span(A[i] & shore for i in bits(cut))) <= 4
        return {"status":"cut","cut":cut}
    history = []
    flipped = 0
    while live & ~(P|Q):
        v = next(bits(live & ~(P|Q)))
        keep = live ^ (1 << v)
        if separator(B,keep,P,Q) is not None:
            neighbors = B[v] & keep
            u = neighbors.bit_length()-1 if v % 2 else next(bits(neighbors))
            history.append(("pivot",B,v,u))
            B = edge_pivot(B,v,u)
            flipped ^= (1 << v) | (1 << u)
            assert separator(B,keep,P,Q) is None
        history.append(("delete",B,v,None))
        B = [row & keep if keep >> i & 1 else 0 for i,row in enumerate(B)]
        live = keep
    x = P & ~flipped
    target = P & flipped
    choices = [x | (s << n) for s in range(8) if image(B,x | (s << n)) & P == target]
    assert len(choices) == 1
    x = choices[0]
    y = image(B,x)
    for op,old,i,j in reversed(history):
        if op == "pivot":
            pair = (1 << i) | (1 << j)
            x,y = (x & ~pair) | (y & pair), (y & ~pair) | (x & pair)
        else:
            y |= dot(old[i],x) << i
        assert image(old,x) == y
    s,t = x >> n,y >> n
    assert dot(s,t) == 0 and x & P == P and not x & y & W
    physical = (x & W) | reps[s,t]
    assert not physical & image(A,physical) and physical & P == P
    return {"status":"witness","witness":physical,"ports":(s,t),
            "pivots":[(i,j) for op,_,i,j in history if op == "pivot"]}


def check():
    from random import Random
    yes = [170,449,240,97,356,477,446,359,242]
    no = [170,449,240,81,300,341,174,327,178]
    pins = [0,1,2]
    for A,want in ((yes,"witness"),(no,"declined")):
        result = link(A,pins,list(range(3,9)),6)
        assert result["status"] == want
        if want == "witness":
            assert result["witness"] in (95,175)
        else:
            assert result["states"] == 35
        print("nine sites",result)
    for n in (20,21):
        full = (1 << n)-1
        A = [full ^ mask({i,(i-1)%n,(i+1)%n}) for i in range(n)]
        result = link(A,pins,list(range(3,n)),3)
        if result["status"] == "witness":
            assert n % 2 and result["witness"] == full
        else:
            assert result["status"] == "declined"
        print("complement cycle",n,result)
    rng = Random(1343)
    coverage = set()
    for case in range(150):
        n = 13
        A = [0]*n
        cross = [1 << i for i in range(3)]
        if case%3:
            cross = [(1 << (3+i)) | rng.randrange(8) for i in range(3)]
        if case%7 == 0:
            cross = [1 << (3+i) for i in range(3)]
        for i,j in combinations(range(6),2):
            if rng.randrange(2) and (case%7 or i//3 == j//3):
                A[i] |= 1 << j
                A[j] |= 1 << i
        for color in range(1,8):
            i = 5+color
            for j in range(3):
                if color >> j & 1:
                    A[i] ^= cross[j]
            for j in bits(A[i]):
                A[j] |= 1 << i
        result = link(A,pins,list(range(6,n)),1)
        coverage.add(result["status"])
        if result["status"] == "witness":
            s,t = result["ports"]
            if s&t:
                coverage.add("non-pointwise")
            for a,b in result["pivots"]:
                if a in pins or b in pins:
                    coverage.add("pin-pivot")
                if max(a,b) >= n:
                    coverage.add("port-pivot")
    print("planted coverage",sorted(coverage))
    assert coverage == {"cut","witness","pin-pivot","port-pivot","non-pointwise"}


if __name__ == "__main__":
    check()
