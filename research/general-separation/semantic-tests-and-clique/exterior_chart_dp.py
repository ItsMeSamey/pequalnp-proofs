"""Construct one labeled link trace, then enumerate attainable six-bit port states.

exterior_states(A,pins,ports) expects the simple auxiliary graph in original
labels, three pins and three independent ports. It returns None for a failed
rank-three link, or one original exterior input mask per attainable port word.
Bits 0..2 of the word are the port inputs, bits 3..5 their outputs.
"""
from itertools import combinations
from random import Random
from rooted_full_boundary_solver import separator, edge_pivot, bits, mask, image, dot


def word(A,x,ports):
    y = image(A,x)
    return sum(((x >> p & 1) | ((y >> p & 1) << 3)) << i for i,p in enumerate(ports))


def pairing(u,v):
    return dot(u & 7,v >> 3) ^ dot(u >> 3,v & 7)


def clamp_trace(A,P,Q):
    live = (1 << len(A))-1
    if separator(A,live,P,Q) is not None:
        return None
    B = A[:]
    swaps = 0
    clamps = []
    while live & ~(P|Q):
        i = next(bits(live & ~(P|Q)))
        keep = live ^ (1 << i)
        if separator(B,keep,P,Q) is not None:
            neighbors = B[i]&keep
            j = neighbors.bit_length()-1 if i%2 else next(bits(neighbors))
            B = edge_pivot(B,i,j)
            swaps ^= (1 << i) | (1 << j)
            assert separator(B,keep,P,Q) is None
        clamps.append((i, swaps >> i & 1))
        B = [row & keep if keep >> v & 1 else 0 for v,row in enumerate(B)]
        live = keep
    return clamps


def inverse(rows):
    n = len(rows)
    work = [r | (1 << (n+i)) for i,r in enumerate(rows)]
    for i in range(n):
        p = next(j for j in range(i,n) if work[j] >> i & 1)
        work[i],work[p] = work[p],work[i]
        for j in range(n):
            if j != i and work[j] >> i & 1:
                work[j] ^= work[i]
    return [r >> n for r in work]


def ordered_components(H):
    # Reachability bitsets, followed by a source-first topological order.
    reach = [1 << i for i in range(len(H))]
    for i,row in enumerate(H):
        for j in bits(row):
            reach[j] |= 1 << i
    for i in range(len(H)):
        for j in range(len(H)):
            if reach[j] >> i & 1:
                reach[j] |= reach[i]
    live = (1 << len(H))-1
    while live:
        for i in bits(live):
            block = sum(1 << j for j in bits(live) if (reach[i] >> j) & (reach[j] >> i) & 1)
            if all(not (H[j] & live & ~block) for j in bits(block)):
                break
        else:
            raise AssertionError("component order")
        yield block
        live ^= block


def exterior_states(A,pins,ports,stats=None):
    P,Q = mask(pins),mask(ports)
    clamps = clamp_trace(A,P,Q)
    if clamps is None:
        return None
    m = len(clamps)
    fixed = [1 << p for p in pins] + [A[p] for p in pins]
    base = [A[i] if swapped else 1 << i for i,swapped in clamps]
    alternate = [1 << i if swapped else A[i] for i,swapped in clamps]
    back = inverse(base + fixed)
    def recover(z):
        return image(back,z | (7 << m))
    x0 = recover(0)
    a = image(alternate,x0)
    w0 = word(A,x0,ports)
    columns = [recover(1 << j) ^ x0 for j in range(m)]
    C = [word(A,col,ports) for col in columns]
    H = [sum(dot(row,col) << j for j,col in enumerate(columns)) for row in alternate]
    assert all(((H[i] >> j) ^ (H[j] >> i)) & 1 == pairing(C[i],C[j])
               for i in range(m) for j in range(m))
    states = {0:0}
    sizes = []
    previous = 0
    coupled = False
    for block in ordered_components(H):
        coupled |= any(H[i] & previous for i in bits(block))
        previous |= block
        sizes.append(block.bit_count())
        placements = list(bits(block))
        new = {}
        for sigma,old in states.items():
            for choice in range(1 << len(placements)):
                u = sum(((choice >> j)&1) << v for j,v in enumerate(placements))
                if any(((a >> i)&1) ^ dot(H[i],u) ^ pairing(C[i],sigma) for i in bits(u)):
                    continue
                value = sigma
                for i in bits(u):
                    value ^= C[i]
                new.setdefault(value,old | u)
        states = new
    answer = {}
    for sigma,z in states.items():
        x = recover(z)
        y = image(A,x)
        assert (x&P) == P and not (y&P) and not (x&y&~Q)
        assert word(A,x,ports) == w0 ^ sigma
        answer[w0 ^ sigma] = x & ~Q
    if stats is not None:
        stats.update(blocks=sizes,baseline=w0,clamps=clamps,coupled_components=coupled)
    return answer


def direct(A,pins,ports):
    P,Q = mask(pins),mask(ports)
    result = set()
    for x in range(1 << len(A)):
        if x&P != P:
            continue
        y = image(A,x)
        if not (y&P) and not (y&x&~Q):
            result.add(word(A,x,ports))
    return result


def check():
    pins,ports = (0,1,2),(3,4,5)
    nine = [170,449,240,81,300,341,174,327,178]
    aux = [r&7 for r in nine[:3]]+[0]*3
    for i in range(3):
        aux[i] |= 1 << (3+i)
        aux[3+i] = 1 << i
    demands = exterior_states(aux,pins,ports)
    inner = set()
    for x in range(0,512,8):
        y = image(nine,x)
        for t in range(8):
            if not (image(nine,x|t) & x):
                inner.add((y&7) | (t << 3))
    assert len(inner) == 35 and len(demands) == 1 and inner.isdisjoint(demands)
    print("nine-site missing state",list(demands),"inner states",len(inner))
    rng = Random(4231)
    coverage = set()
    accepted = 0
    for case in range(90):
        n = 6 + (case%7)
        ports = tuple(range(n-3,n))
        A = [0]*n
        for i,j in combinations(range(n),2):
            if i not in ports and rng.randrange(2):
                A[i] |= 1 << j
                A[j] |= 1 << i
        stats = {}
        answers = exterior_states(A,pins,ports,stats)
        if answers is None:
            continue
        accepted += 1
        assert set(answers) == direct(A,pins,ports)
        for code,physical in answers.items():
            x = physical | sum(((code >> j)&1) << v for j,v in enumerate(ports))
            assert word(A,x,ports) == code
        if len(answers)>1:
            coverage.add("extra states")
        if len(stats["blocks"])>1:
            coverage.add("multiple components")
        if stats["coupled_components"] and len(answers)>1 and n>=10:
            coverage.add("coupled component chain")
        if any(s for _,s in stats["clamps"]):
            coverage.add("output clamps")
        base_rows = [A[i] if s else 1 << i for i,s in stats["clamps"]]
        fixed_rows = [1 << p for p in pins] + [A[p] for p in pins]
        for j,(i,s) in enumerate(stats["clamps"]):
            changed = base_rows[:]
            changed[j] = 1 << i if s else A[i]
            try:
                inverse(changed+fixed_rows)
            except StopIteration:
                coverage.add("singular alternative")
    assert len(coverage) == 5
    print("seeded linked comparisons",accepted,"of 90",sorted(coverage))


if __name__ == "__main__":
    check()
