"""Full-precision center jets for parity vertices and edge COPY tensors."""
from itertools import combinations, product
from math import comb

from all_center_packet_jets import JetRing
from packet_entry_tape import Ring
from variable_packet_machine import shifted_kernel


def _width(base_rows, owner, n):
    neighbors = [set() for _ in range(n)]
    for rows in base_rows:
        ends = {owner[row] for row in rows}
        for v in ends:
            neighbors[v].update(ends - {v})
    width = 0
    for v, live in enumerate(neighbors):
        width = max(width, len(live))
        for u in live:
            neighbors[u].remove(v)
            neighbors[u].update(live - {u})
    return width


def _sum_spins(factors, n, mod):
    """Scopes are elimination positions, smallest first and low bit first."""
    buckets = [[] for _ in range(n)]
    answer = 1
    for scope, values in factors:
        if scope:
            buckets[scope[0]].append((scope, values))
        else:
            answer = answer * values[0] % mod
    for index, bucket in enumerate(buckets):
        if not bucket:
            answer = 2 * answer % mod
            continue
        scope = sorted({u for s, _ in bucket for u in s})
        assert scope[0] == index
        parts = [([scope.index(u) for u in s], values) for s, values in bucket]
        output = [0] * (1 << (len(scope) - 1))
        for word in range(1 << len(scope)):
            weight = 1
            for positions, values in parts:
                local = sum(((word >> pos) & 1) << j for j, pos in enumerate(positions))
                weight = weight * values[local] % mod
            output[word >> 1] = (output[word >> 1] + weight) % mod
        bucket.clear()
        if len(scope) > 1:
            buckets[scope[1]].append((tuple(scope[1:]), output))
        else:
            answer = answer * output[0] % mod
    return answer


def evaluate(edges, packets, *, center, count, precision, order, parity=None, sign=0,
             width_cap=None, term_cap=None):
    """Return (scalar coefficients at zeta=0, stats) or None on preflight decline.

    count is the number of coefficients. order lists original vertex names.
    Working-ring sign bits are the 2e row bits followed by e edge bits.
    """
    edges = tuple(tuple(edge) for edge in edges)
    packets = tuple(tuple(packet) for packet in packets)
    order = tuple(order)
    e = len(edges)
    if not e or any(len(edge) != 2 or edge[0] == edge[1] for edge in edges):
        raise ValueError("expected nonempty loopless edges")
    if not packets:
        raise ValueError("empty packet schedule")
    length = len(packets[0])
    if length < 2 or length & (length-1) or any(len(pk) != length for pk in packets):
        raise ValueError("expected uniform power-of-two packet lengths")
    ports = [p for pk in packets for p in pk if p is not None]
    if any(type(p) is not int for p in ports) or sorted(ports) != list(range(2*e)):
        raise ValueError("each original port must occur exactly once")
    if not -length <= center < length or count < 1 or precision < 1:
        raise ValueError("invalid center or requested precision")
    if not 0 <= sign < 1 << (3*e) or any(x is not None and x < 0 for x in (width_cap, term_cap)):
        raise ValueError("invalid character or cap")
    vertices = {v for edge in edges for v in edge}
    if len(order) != len(vertices) or set(order) != vertices:
        raise ValueError("order must be a permutation of all vertices")
    parity = {} if parity is None else parity
    if set(parity) - vertices or any(b not in (0,1) for b in parity.values()):
        raise ValueError("invalid parity targets")
    vcount = len(order)
    position = {v:i for i,v in enumerate(order)}
    owner = [position[v] for edge in edges for v in edge]
    base_rows = [[] for _ in edges]
    for pk in packets:
        for i, row in enumerate(pk):
            j = i + center
            if row is not None and 0 <= j < length and pk[j] is not None:
                base_rows[pk[j]//2].append(row)
    width = _width(base_rows, owner, vcount)
    limit = sum(comb(2*e,k)*length**k for k in range(min(count-1,2*e)+1))
    if (width_cap is not None and width > width_cap) or (term_cap is not None and limit > term_cap):
        return None
    mod = 1 << (precision + vcount)
    base = Ring(precision + vcount, (0,), 1)
    ring = JetRing(base, count)
    point = (0,) if count == 1 else (0,1) + (0,)*(count-2)
    kernel = {d:shifted_kernel(ring,length,center,point,d) for d in range(1-length,length)}
    # The remaining grid endpoint has no matching physical offset or base row.
    c = kernel[center][0] if center in kernel else 0
    lam = (1-2*c) % mod
    changes = [[] for _ in range(2*e)]
    for pk in packets:
        for i, row in enumerate(pk):
            if row is None:
                continue
            grouped = {}
            for j,col in enumerate(pk):
                if col is None:
                    continue
                # Subtract each entry's entire constant, including the matched unit.
                delta = (0,) + kernel[j-i][1:]
                x = col//2
                grouped[x] = ring.add(grouped.get(x,ring.scalar(0)),delta)
            changes[row] = [(x,d) for x,d in grouped.items() if any(d)]

    row_sign = [(sign >> i) & 1 for i in range(2*e)]
    edge_sign = [(-1)**((sign >> (2*e+j)) & 1) for j in range(e)]
    total = ring.scalar(0)
    terms = 0
    for k in range(min(count-1,2*e)+1):
        for selected in combinations(range(2*e),k):
            selected_set = set(selected)
            pins = {}
            for i in selected:
                v = owner[i]
                bit = 1 ^ row_sign[i]
                if v in pins and pins[v] != bit:
                    break
                pins[v] = bit
            else:
                unary = []
                for v in range(vcount):
                    values = [0 if v in pins and pins[v] != h else (-1)**(h*parity.get(order[v],0))
                              for h in (0,1)]
                    unary.append(((v,),values))
                for choices in product(*(changes[i] for i in selected)):
                    pinned_edges = {x for x,_ in choices}
                    factors = list(unary)
                    for j,incident in enumerate(base_rows):
                        rows = [i for i in incident if i not in selected_set]
                        scope = tuple(sorted({owner[i] for i in rows}))
                        values = []
                        for h in range(1 << len(scope)):
                            b = sum(row_sign[i] ^ ((h >> scope.index(owner[i])) & 1) for i in rows)
                            values.append(int(j not in pinned_edges) + edge_sign[j]*pow(lam,b,mod))
                        factors.append((scope,values))
                    value = ring.scalar(_sum_spins(factors,vcount,mod) * (-2)**k)
                    for _,d in choices:
                        value = ring.mul(value,d)
                    total = ring.add(total,value)
                    terms += 1
    guard = 1 << vcount
    if any(c % guard for c in total):
        raise ArithmeticError("Fourier numerator violates integrality")
    return tuple(c//guard for c in total), {"width":width,"terms":terms,"term_bound":limit}
