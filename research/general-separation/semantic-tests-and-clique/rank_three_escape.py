"""Return (YES, local mask), (NO,None), or (UNKNOWN,None) for one chart block."""
from itertools import combinations
from random import Random
from low_rank_exterior_dp import coordinates, low_transitions, quad
from exterior_chart_dp import bits, dot, image, mask, ordered_components, pairing
from supplied_cut_reducer import even, path


def mixed(M,a,read):
    """Find a feasible support with readout one in a symmetric mixed prescription."""
    n = len(M)
    A = [r & ~(1 << i) for i,r in enumerate(M)]
    parity = a ^ sum(((r >> i)&1) << i for i,r in enumerate(M))
    neutral = set(range(n))-set(bits(parity))
    for i in neutral:
        if read >> i & 1:
            return 1 << i
    # With zero readout on all even sites, a readout-one spanning path segment
    # has two odd endpoints of different readout and only even internal sites.
    return path(A,set(bits(parity & read)),set(bits(parity & ~read)),neutral)


def syndrome(C,x):
    s = 0
    for i in bits(x):
        s ^= C[i]
    return s


def escape(M,a,C,w0,brute_budget=None):
    basis,values,labels = coordinates(C)
    k = len(basis)
    def answer(x):
        if x is None:
            return "NO",None
        assert syndrome(C,x) and not x & (a ^ image(M,x))
        return "YES",x
    if k <= 2:
        return answer(next((x for d,x in low_transitions(M,C,w0,0) if d),None))
    if k == 3:
        forms = range(1,8)
        read = [mask(i for i,l in enumerate(labels) if dot(f,l)) for f in range(8)]
        def Q(x):
            return quad(w0 ^ values[x])
        def J(x,y):
            return pairing(values[x],values[y])
        if not any(J(x,y) for x,y in combinations(range(8),2)):
            for f in forms:
                x = mixed(M,a,read[f])
                if x is not None:
                    return answer(x)
            return answer(None)
        pairs = [(f,g) for f,g in combinations(forms,2) if all(
            J(x,y) == ((dot(f,x)&dot(g,y)) ^ (dot(g,x)&dot(f,y)))
            for x,y in combinations((1,2,4),2))]
        def shear(rows,cols):
            return [row ^ (cols if rows >> i & 1 else 0) for i,row in enumerate(M)]
        f,g = pairs[0]
        for p,r in ((read[f],read[g]),(read[g],read[f])):
            x = mixed(shear(r,p),a ^ r,p)
            if x is not None:
                return answer(x)
        radical = next(x for x in forms if not any(J(x,y) for y in forms))
        if Q(radical):
            return answer(None)
        for f,g in pairs:
            if all(Q(x) == (dot(f,x) & dot(g,x)) for x in range(8)):
                for p,r in ((read[f],read[g]),(read[g],read[f])):
                    simple = [row & ~(1 << i) for i,row in enumerate(shear(r,p))]
                    for h in (1,2,4):
                        colors = [((p >> i)&1) | (dot(h,v)<<1) for i,v in enumerate(labels)]
                        x = even(simple,colors,2)
                        if x is not None:
                            return answer(x)
                return answer(None)
    if brute_budget is not None and len(C) <= brute_budget:
        return answer(next((x for x in range(1,1 << len(C))
                            if syndrome(C,x) and not x & (a ^ image(M,x))),None))
    return "UNKNOWN",None


def check():
    rng = Random(992)
    types = {}
    for _ in range(900):
        n = 6
        basis = []
        while len(basis)<3:
            v = rng.randrange(1,64)
            if v not in coordinates(basis)[1]:
                basis.append(v)
        vals = coordinates(basis)[1]
        C = basis + rng.choices(vals,k=n-3)
        w0 = rng.choice([w for w in range(64) if not quad(w)])
        rad = [v for v in vals if not any(pairing(v,y) for y in vals)]
        zeros = sum(not quad(w0 ^ v) for v in vals)
        typ = ("zero polar" if len(rad)==8 else "odd radical" if quad(w0 ^ rad[1])
               else "split" if zeros==6 else "anisotropic")
        M = [rng.randrange(1 << n) for _ in C]
        for i,j in combinations(range(n),2):
            M[j] ^= ((((M[i] >> j) ^ (M[j] >> i))&1) ^ pairing(C[i],C[j])) << i
        a = sum((quad(w0 ^ v) ^ ((M[i] >> i)&1)) << i for i,v in enumerate(C))
        truth = any(syndrome(C,x) and not x & (a ^ image(M,x)) for x in range(1 << n))
        status,_ = escape(M,a,C,w0)
        if typ == "anisotropic":
            assert status == "UNKNOWN"
            status,_ = escape(M,a,C,w0,n)
        assert (status == "YES") == truth
        types[typ] = types.get(typ,0)+1
    assert len(types) == 4
    # An induced path whose odd endpoints have different readouts.
    assert mixed([2,5,2],5,1) == 7
    for k in range(3):
        C = list(range(1 << k))*2
        M = [0]*len(C)
        assert (escape(M,0,C,0)[0] == "YES") == bool(k)
    C = [1,2,4]*40
    M = [((1 << len(C))-1) ^ (1 << i) for i in range(len(C))]
    assert list(ordered_components(M)) == [(1 << len(C))-1]
    assert len(coordinates(C)[0]) == 3 and escape(M,0,C,0)[0] == "YES"
    print(types,"; rank 0/1/2, mixed path, and 120-site rank-three SCC passed")


if __name__ == "__main__":
    check()
