"""Low-precision exact t=1 contraction on parity vertices and edge-COPY columns."""
from itertools import combinations, product
from variable_packet_machine import shifted_kernel


def character_sum(n, equations, sign):
    """Sum (-1)^(sign·x) on an affine GF(2) fiber."""
    pivots = {}
    for mask, rhs in equations:
        while mask:
            i = mask.bit_length()-1
            if i not in pivots:
                pivots[i] = mask, rhs
                break
            row, bit = pivots[i]
            mask ^= row
            rhs ^= bit
        if not mask and rhs:
            return 0
    phase = 0
    while sign:
        i = sign.bit_length()-1
        if i not in pivots:
            return 0
        row, bit = pivots[i]
        sign ^= row
        phase ^= bit
    size = 1 << (n-len(pivots))
    return -size if phase else size


def evaluate(edges, packets, ring, zeta, *, parity=None, sign=0):
    """Port 2j+b is endpoint b of edge j. Coordinate order: all y ports, then x edges.

    parity maps original vertex IDs to required XOR (default zero); sign is a
    character bitmask in the stated coordinate order. Packets are supplied,
    each entry a port ID or None. Returns (ring element, charged term counts).
    """
    edges = tuple(tuple(e) for e in edges)
    packets = tuple(tuple(pk) for pk in packets)
    e = len(edges)
    if not e or not packets or any(len(edge)!=2 or edge[0]==edge[1] for edge in edges):
        raise ValueError("expected nonempty loopless edge list")
    L = len(packets[0])
    if L < 2 or L & (L-1) or any(len(pk)!=L for pk in packets):
        raise ValueError("expected uniform power-of-two packet lengths")
    ports = [i for pk in packets for i in pk if i is not None]
    if any(type(i) is not int for i in ports) or sorted(ports)!=list(range(2*e)):
        raise ValueError("physical ports must occur exactly once")
    if not 0 <= sign < 1 << (3*e) or ring.p<1:
        raise ValueError("invalid sign or precision")
    vertices = {}
    for j,edge in enumerate(edges):
        for b,v in enumerate(edge):
            vertices[v]=vertices.get(v,0) | (1<<(2*j+b))
    parity = {} if parity is None else parity
    if set(parity)-vertices.keys() or any(b not in (0,1) for b in parity.values()):
        raise ValueError("invalid vertex parity")
    old=[(row,parity.get(v,0)) for v,row in vertices.items()]
    kmax=min(2*e,ring.p-(e-len(vertices))-1)
    zero=ring.scalar(0)
    stats={'orders':0,'row_sets':0,'terms':0,'nonzero_terms':0,'kernel_entries':0}
    if kmax<0:
        return zero,stats
    kernel={d:shifted_kernel(ring,L,1,zeta,d) for d in range(1-L,L)}
    stats['kernel_entries']=len(kernel)
    ties=[None]*(2*e)
    correction=[None]*(2*e)
    for pk in packets:
        for i,row in enumerate(pk):
            if row is None:
                continue
            successor=pk[i+1] if i+1<L else None
            mask=0 if successor is None else 1<<(2*e+successor//2)
            ties[row]=((1<<row)|mask,0)
            by_edge={}
            for j,col in enumerate(pk):
                if col is None:
                    continue
                coef=kernel[j-i]
                if j==i+1:
                    coef=ring.add(coef,ring.scalar(-1))
                if any(x&1 for x in coef):
                    raise ArithmeticError("native kernel disagrees with mod-two partial shift")
                x=col//2
                by_edge[x]=ring.add(by_edge.get(x,zero),coef)
            correction[row]=[(x,c) for x,c in by_edge.items() if c!=zero]
    total=zero
    for k in range(kmax+1):
        stats['orders']+=1
        for defects in combinations(range(2*e),k):
            stats['row_sets']+=1
            defect_mask=sum(1<<i for i in defects)
            equalities=old+[t for i,t in enumerate(ties) if not (defect_mask>>i)&1]
            for choices in product(*(correction[i] for i in defects)):
                stats['terms']+=1
                pins=[(1<<(2*e+x),1) for x,_ in choices]
                mass=character_sum(3*e,equalities+pins,sign^defect_mask)
                coef=ring.scalar(-mass if k%2 else mass)
                for _,w in choices:
                    coef=ring.mul(coef,w)
                if coef!=zero:
                    stats['nonzero_terms']+=1
                    total=ring.add(total,coef)
    return total,stats
