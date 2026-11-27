"""Exhaustive chart controls, capped at ten original clamp bits."""
from collections import deque
from itertools import combinations
from one_missing_reservoir_check import host, signal, representatives, FIXTURE, B
from exterior_chart_dp import bits, dot, image, inverse, mask
from rank_three_escape import syndrome
from three_pin_template_solver import basis_of, kernel


def examine(H,a,C):
    n = len(H)
    if n > 10:
        raise ValueError("exhaustive regression limit: ten clamps")
    limit = 1 << n
    directions = [mask(group) for k in range(1,min(n,4)+1)
                  for group in combinations(range(n),k)]
    def legal(z):
        return not z & (image(H,z)^a)
    escapes = [z for z in range(limit) if legal(z) and syndrome(C,z)]
    skew = [sum(((((row >> j) ^ (H[j] >> i))&1) << j) for j in range(n))
            for i,row in enumerate(H)]
    rank = len(basis_of(skew))
    assert rank <= 2
    regular = {}
    successes = {}
    singular = 0
    for T in range(limit):
        rows = [H[i] if T >> i & 1 else 1 << i for i in range(n)]
        kernels = kernel(rows,n)
        if kernels:
            if len(kernels)==1 and syndrome(C,kernels[0]) and not image(skew,kernels[0]) & T:
                # The direct certificate requires Q(Ck)=0; verify compatibility.
                if not dot(a&T,kernels[0]):
                    candidates = [x for x in range(limit) if image(rows,x)==(a&T)]
                    assert len(candidates)==2
                    assert any(x in escapes for x in candidates)
                    singular += 1
            continue
        back = inverse(rows)
        regular[T] = back
        alternate = [1 << i if T >> i & 1 else H[i] for i in range(n)]
        new = [sum(dot(row,image(back,1 << j)) << j for j in range(n)) for row in alternate]
        new_skew = [sum(((((r >> j) ^ (new[j] >> i))&1) << j) for j in range(n))
                    for i,r in enumerate(new)]
        assert len(basis_of(new_skew)) == rank
        for small in [0]+[1 << j for j in range(n)]:
            z = image(back,small ^ (a&T))
            if legal(z) and syndrome(C,z):
                successes[T] = z
                break
    distance = {0:0}
    queue = deque([0])
    while queue:
        t = queue.popleft()
        for d in directions:
            nxt = t ^ d
            if nxt in regular and nxt not in distance:
                distance[nxt] = distance[t]+1
                queue.append(nxt)
    assert len(distance)==len(regular) and max(distance.values()) <= n
    if escapes:
        S = min(escapes,key=int.bit_count)
        if S in regular:
            assert S in successes
        else:
            family = kernel([H[i] & S if S >> i & 1 else 1 << i for i in range(n)],n)
            assert len(family)==1
            j = next(bits(family[0]))
            assert S ^ (1 << j) in successes
        radius = min(distance[t] for t in successes)
        assert S.bit_count() <= 4*radius+1
    else:
        radius = None
        assert not successes
    return len(regular),max(distance.values()),radius,singular,successes


def cycle(n):
    full = (1 << n)-1
    A = [full ^ mask({i,(i-1)%n,(i+1)%n}) for i in range(n)]
    colors = [1,2,7]+[0]*(n-3)
    G = host(A,colors)
    R,V = zip(*(signal(v) for v in colors))
    C = [r | (v << 3) for r,v in zip(R,V)]
    H = [(G[i+9] >> 9) ^ sum(dot(V[i],r) << j for j,r in enumerate(R)) for i in range(n)]
    a = sum((dot(r,7)^dot(v,3)) << i for i,(r,v) in enumerate(zip(R,V)))
    counts = examine(H,a,C)
    for z in counts[-1].values():
        original = 7 | (representatives()[7,5]<<3) | (z<<9)
        assert not original & image(G,original) and z==full
    assert bool(counts[-1]) == bool(n%2)
    print("cycle",n,"regular/eccentricity/escape radius/singular certificates",counts[:-1])


def ten():
    G = [170,449,240,81,812,853,686,839,178,240]
    counts = examine([0],0,[4<<3])
    assert counts[:4]==(1,0,0,1)
    for z in counts[-1].values():
        w = 7 | (representatives()[3,3]<<3) | (z<<9)
        assert w in (615,663,967) and not w & image(G,w)
    print("ten-site",counts[:4])
    for t in (1,2,3):
        C = [v for v in (4<<3,3<<3,3 | (7<<3)) for _ in range(t)]
        n = len(C)
        H = [((1<<n)-1) ^ (1<<i) for i in range(n)]
        results = examine(H,0,C)
        # Construct actual 3+9t-site host and replay every returned mask.
        physical = [0]*(3+9*t)
        def edge(i,j):
            physical[i] |= 1 << j
            physical[j] |= 1 << i
        edge(0,1)
        for i in range(6*t):
            v = i//t
            for p in bits(B[v]):
                edge(p,3+i)
            for j in range(i):
                if FIXTURE[v+3] >> (3+j//t)&1:
                    edge(3+j,3+i)
        offset = 3+6*t
        for i,col in enumerate(C):
            for p in bits(col&7):
                edge(offset+i,p)
            for j in range(6*t):
                if dot(col>>3,B[j//t]):
                    edge(offset+i,3+j)
            for j in range(i):
                edge(offset+i,offset+j)
        reps = representatives()
        for z in results[-1].values():
            w = 59 ^ syndrome(C,z)
            u = reps[w&7,w>>3]
            original = 7 | mask(3+j*t for j in bits(u)) | (z<<offset)
            assert not original & image(physical,original)
        print("blowup",t,results[:4])


if __name__ == "__main__":
    ten()
    for n in range(4,11):
        cycle(n)
