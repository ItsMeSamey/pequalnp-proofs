"""Linked exterior solver with polynomial transitions for port rank <=2."""
from itertools import combinations
from random import Random
from exterior_chart_dp import (bits, clamp_trace, direct, dot, image, inverse, mask,
                               ordered_components, pairing, word)
from supplied_cut_reducer import even


def quad(x):
    return dot(x & 7,x >> 3)


def coordinates(cols):
    values = [0]
    basis = []
    for v in cols:
        if v not in values:
            basis.append(v)
            values += [x ^ v for x in values]
    return basis,values,[values.index(v) for v in cols]


def bilinear(rows,v,w):
    return dot(v,image(rows,w))


def low_transitions(H,cols,w0,sigma):
    basis,values,labels = coordinates(cols)
    k = len(basis)
    assert k <= 2
    R = [sum((quad(v) if i == j else pairing(v,basis[j])) << j
             for j in range(i,k)) for i,v in enumerate(basis)]
    simple = [row ^ sum(bilinear(R,v,w) << j for j,w in enumerate(labels))
              for row,v in zip(H,labels)]
    for i in range(len(simple)):
        simple[i] &= ~(1 << i)
    base = sum(pairing(v,w0 ^ sigma) << i for i,v in enumerate(basis))
    for e,d in enumerate(values):
        lam = base ^ image(R,e)
        if dot(e,lam):
            continue
        T = [lam & ~e & (1 << i) for i in range(k)]
        ones = list(bits(lam & e))
        for i,j in zip(ones[::2],ones[1::2]):
            T[i] |= 1 << j
            T[j] |= 1 << i
        adjusted = [row ^ sum(bilinear(T,v,w) << j for j,w in enumerate(labels) if i != j)
                    for i,(row,v) in enumerate(zip(simple,labels))]
        u = even(adjusted,labels,e)
        if u is not None:
            yield d,u


def transfer(H,a,C,w0):
    states = {0:0}
    for block in ordered_components(H):
        slots = list(bits(block))
        local = [sum(((H[i] >> j)&1) << t for t,j in enumerate(slots)) for i in slots]
        cols = [C[i] for i in slots]
        rank = len(coordinates(cols)[0])
        nxt = {}
        for sigma,prior in states.items():
            if rank <= 2:
                choices = low_transitions(local,cols,w0,sigma)
            else:
                def enumerate_choices():
                    for u in range(1 << len(slots)):
                        if any(((a >> slots[i])&1) ^ dot(local[i],u) ^ pairing(cols[i],sigma)
                               for i in bits(u)):
                            continue
                        d = 0
                        for i in bits(u):
                            d ^= cols[i]
                        yield d,u
                choices = enumerate_choices()
            for d,u in choices:
                lifted = mask(slots[i] for i in bits(u))
                nxt.setdefault(sigma ^ d,prior | lifted)
        states = nxt
    return {w0 ^ s:z for s,z in states.items()}


def exterior_states(A,pins,ports):
    clamps = clamp_trace(A,mask(pins),mask(ports))
    if clamps is None:
        return None
    m = len(clamps)
    fixed = [1 << p for p in pins] + [A[p] for p in pins]
    base = [A[i] if s else 1 << i for i,s in clamps]
    other = [1 << i if s else A[i] for i,s in clamps]
    back = inverse(base + fixed)
    x0 = image(back,7 << m)
    cols = [image(back,1 << j) for j in range(m)]
    H = [sum(dot(row,c) << j for j,c in enumerate(cols)) for row in other]
    states = transfer(H,image(other,x0),[word(A,c,ports) for c in cols],word(A,x0,ports))
    result = {}
    Q = mask(ports)
    for state,z in states.items():
        x = image(back,z | (7 << m))
        assert word(A,x,ports) == state and not (x & image(A,x) & ~Q)
        result[state] = x & ~Q
    return result


def check():
    rng = Random(351)
    for k in range(3):
        for _ in range(80):
            n = 6
            L = []
            while len(L) < k:
                v = rng.randrange(1,64)
                if v not in coordinates(L)[1]:
                    L.append(v)
            colors = L + rng.choices(coordinates(L)[1],k=n-k)
            H = [rng.randrange(1 << n) for _ in colors]
            for i,j in combinations(range(n),2):
                bit = ((H[i] >> j)&1) ^ pairing(colors[i],colors[j])
                H[j] = (H[j] & ~(1 << i)) | (bit << i)
            w0,sigma = rng.randrange(64),rng.randrange(64)
            a = sum((quad(v) ^ pairing(v,w0) ^ ((H[i] >> i)&1)) << i for i,v in enumerate(colors))
            wanted = {}
            for u in range(1 << n):
                if any(((a >> i)&1) ^ dot(H[i],u) ^ pairing(colors[i],sigma) for i in bits(u)):
                    continue
                d = 0
                for i in bits(u):
                    d ^= colors[i]
                wanted.setdefault(d,set()).add(u)
            got = dict(low_transitions(H,colors,w0,sigma))
            assert got.keys() == wanted.keys() and all(u in wanted[d] for d,u in got.items())
    n = 100
    C = [1,2,3,0]*(n//4)
    H = [((1 << n)-1) ^ (1 << i) for i in range(n)]
    assert list(ordered_components(H)) == [(1 << n)-1]
    assert transfer(H,0,C,0).keys() == {0,1,2,3}
    # Rank six in the first SCC, rank two in a second. Enforce the required
    # symplectic relation across the one-directional component boundary.
    C = [1,2,4,8,16,32,1,3]
    n = len(C)
    H = [1 << i for i in range(n)]
    for i,j in combinations(range(n),2):
        forward = int((i<6) == (j<6))
        H[i] |= forward << j
        H[j] |= (forward ^ pairing(C[i],C[j])) << i
    def profile(rows,cols):
        return {(block,len(coordinates([cols[i] for i in bits(block)])[0]))
                for block in ordered_components(rows)}
    initial = profile(H,C)
    assert initial == {(63,6),(192,2)}
    flips = 0
    for chosen in range(1 << n):
        rows = [H[i] if chosen >> i & 1 else 1 << i for i in range(n)]
        try:
            back = inverse(rows)
        except StopIteration:
            continue
        other = [1 << i if chosen >> i & 1 else H[i] for i in range(n)]
        new_H = [0]*n
        new_C = []
        for j in range(n):
            old = image(back,1 << j)
            col = 0
            for i in bits(old):
                col ^= C[i]
            new_C.append(col)
            for i in range(n):
                new_H[i] |= dot(other[i],old) << j
        assert profile(new_H,new_C) == initial
        flips += 1
    linked = 0
    for _ in range(45):
        n = rng.randint(6,11)
        pins,ports = (0,1,2),tuple(range(n-3,n))
        A = [0]*n
        for i,j in combinations(range(n),2):
            if i not in ports and rng.randrange(2):
                A[i] |= 1 << j
                A[j] |= 1 << i
        answers = exterior_states(A,pins,ports)
        if answers is not None:
            assert answers.keys() == direct(A,pins,ports)
            linked += 1
    print("240 low-rank transitions; 100-site rank-two SCC; admissible rank-six chart flips",
          flips,"; raw linked graphs",linked)


if __name__ == "__main__":
    check()
