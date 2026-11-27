"""Monochromatic module quotient and exact affine propagation for target Cz=r.

solve_chart returns YES and a raw clamp mask, NO, or UNKNOWN. physical_payload
wraps the fixed 35-state reduction and returns an original host witness on YES.
"""
from itertools import combinations, product
from random import Random
from bounded_clamp_bfs import bits, dot, image, mask, host, signal, representatives, syndrome
from three_pin_template_solver import kernel


def module(H,colors,i,j):
    chosen = (1 << i) | (1 << j)
    while True:
        extra = 0
        for v in range(len(H)):
            if chosen >> v & 1:
                continue
            incoming = H[v]&chosen
            outgoing = sum(((H[w] >> v)&1)<<w for w in bits(chosen))
            if incoming not in (0,chosen) or outgoing not in (0,chosen):
                if colors[v] != colors[i]:
                    return None
                extra |= 1 << v
        if not extra:
            return chosen
        chosen |= extra


def quotient(H,a,C):
    H = H[:]
    C = C[:]
    origins = list(range(len(C)))
    while True:
        colors = [(c,((a >> i) ^ (H[i] >> i))&1) for i,c in enumerate(C)]
        found = None
        for i,j in combinations(range(len(C)),2):
            if colors[i] == colors[j]:
                found = module(H,colors,i,j)
                if found:
                    break
        if found is None:
            return H,a,C,origins
        sites = list(bits(found))
        assert all(((H[i]>>j) ^ (H[j]>>i))&1 == 0 for i,j in combinations(sites,2))
        rep = sites[0]
        keep = [i for i in range(len(C)) if not found >> i & 1 or i==rep]
        # Using the retained original diagonal preserves its singleton equation.
        H = [sum(((H[i] >> j)&1)<<d for d,j in enumerate(keep)) for i in keep]
        a = sum(((a >> j)&1)<<d for d,j in enumerate(keep))
        C = [C[i] for i in keep]
        origins = [origins[i] for i in keep]


def affine(rows,n):
    basis = {}
    for left,b in rows:
        while left:
            p = left.bit_length()-1
            if p not in basis:
                basis[p] = (left,b)
                break
            v,t = basis[p]
            left ^= v
            b ^= t
        if not left and b:
            return None
    x = 0
    for p,(v,t) in sorted(basis.items()):
        x |= (dot(v,x)^t)<<p
    return x,kernel([v for v,t in basis.values()],n)


def solve_chart(H,a,C,r,stats=None):
    M,b,cols,origins = quotient(H,a,C)
    n = len(cols)
    if stats is not None:
        stats["quotient_size"] = n
    rows = [(sum(((c>>j)&1)<<i for i,c in enumerate(cols)),(r>>j)&1)
            for j in range(max([r.bit_length()]+[c.bit_length() for c in C]))]
    while True:
        result = affine(rows,n)
        if result is None:
            return "NO",None
        x,K = result
        for i,v in enumerate(M):
            left = sum(((w>>i)&1)<<j for j,w in enumerate(K))
            right = sum(dot(w,v)<<j for j,w in enumerate(K))
            l,rhs = (x>>i)&1, dot(v,x)^((b>>i)&1)
            if not left and not right and l and rhs:
                return "NO",None
            if (not left and l and right):
                rows.append((v,(b>>i)&1))
            elif (not right and rhs and left) or (left and left==right and l==rhs):
                rows.append((1<<i,0))
            else:
                continue
            break
        else:
            for w in [x]+[x^v for v in K]:
                if not w & (b^image(M,w)):
                    z = mask(origins[i] for i in bits(w))
                    assert syndrome(C,z)==r and not z & (a^image(H,z))
                    return "YES",z
            return "UNKNOWN",None


def physical_payload(A,colors):
    G = host(A,colors)
    R,V = zip(*(signal(v) for v in colors)) if colors else ([],[])
    C = [r | v<<3 for r,v in zip(R,V)]
    H = [(G[9+i]>>9)^sum(dot(v,r)<<j for j,r in enumerate(R)) for i,v in enumerate(V)]
    a = sum((dot(r,7)^dot(v,3))<<i for i,(r,v) in enumerate(zip(R,V)))
    status,z = solve_chart(H,a,C,4|(2<<3))
    if status != "YES":
        return status,None
    w = 7 | (representatives()[7,5]<<3) | (z<<9)
    assert not w & image(G,w)
    return status,w


def check():
    rng = Random(127)
    counts = {}
    for n in range(3,8):
        for _ in range(25):
            A = [0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    A[i] |= 1<<j
                    A[j] |= 1<<i
            colors = [rng.randrange(8) for _ in A]
            status,w = physical_payload(A,colors)
            actual = any(syndrome(colors,z)==4 and not z & image(A,z) for z in range(1<<n))
            if status != "UNKNOWN":
                assert (status=="YES")==actual
            counts[status] = counts.get(status,0)+1
    for n in (20,21):
        A = [((1<<n)-1)^mask({i,(i-1)%n,(i+1)%n}) for i in range(n)]
        status,_ = physical_payload(A,[1,2,7]+[0]*(n-3))
        assert status == ("YES" if n%2 else "NO")
    # Nine payload groups; independent blowup and clique blowup with symmetric
    # internal perturbations preserve every attainable target in the chart.
    colors = [1,2,7]+[0]*6
    A = [2,1,0]+[0]*6
    assert physical_payload(A,colors)[0] == "NO"
    for t in (1,4,8):
        for dense in (False,True):
            n = t*len(A)
            rows = [0]*n
            for i,j in combinations(range(n),2):
                same = i//t==j//t
                if (dense and same and rng.randrange(4)) or (not same and A[i//t]>>(j//t)&1):
                    rows[i] |= 1<<j
                    rows[j] |= 1<<i
            assert physical_payload(rows,[v for v in colors for _ in range(t)])[0]=="NO"
    stalled = [44,376,249,151,334,71,54,12,18]
    assert physical_payload(stalled,[1,2,7]+[0]*6)[0] == "UNKNOWN"
    # Sampling construction: only marked payload classes and all six reservoir
    # classes are blown up. Test false twins, true twins and irregular internal
    # edges; the fixed representative never selects two inside one class.
    m,t = 33,2
    classes = [i for i in range(m) for _ in range(t if i<3 else 1)]
    for variant in range(3):
        rows = [0]*len(classes)
        for i,j in combinations(range(len(rows)),2):
            u,v = classes[i],classes[j]
            edge = ((u-v)%m not in (1,m-1)) if u!=v else (variant==1 or variant==2 and i%2)
            if edge:
                rows[i] |= 1<<j
                rows[j] |= 1<<i
        colors = [([1,2,7]+[0]*(m-3))[i] for i in classes]
        status,w = physical_payload(rows,colors)
        assert status=="YES"
        G = host(rows,colors)
        copies = [i for i in range(len(G)) for _ in range(t if 3<=i<9 else 1)]
        actual = mask(copies.index(i) for i in bits(w))
        for i in bits(actual):
            assert sum((G[copies[i]]>>copies[j])&1 for j in bits(actual))%2==0
    print("125 small physical comparisons",counts,"; co-cycles 20/21; nine-group blowups to 72 payload sites")


if __name__ == "__main__":
    check()
