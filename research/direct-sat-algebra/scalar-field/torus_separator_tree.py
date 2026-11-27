"""Cut-index dynamic programming on a supplied binary tree of sparse inequations."""
from dataclasses import dataclass
from torus_factor_blocks import lattice_index
from torus_overlap import _monomial, _nonzero, _relations, _values


@dataclass(frozen=True)
class Decision:
    status: str
    max_cut_index: int | None
    peak_states: int


def decide(field, n, rows, constants, polynomials, tree, *, max_overlap=256):
    """Integer leaves identify sparse polynomials; joins are ordered binary pairs."""
    order = field.size - 1
    if n < 0 or max_overlap < 0:
        raise ValueError("invalid dimension or budget")

    def row(ex):
        ex = tuple(ex)
        if len(ex) != n or any(type(v) is not int for v in ex):
            raise ValueError("invalid exponent vector")
        return tuple(v % order for v in ex)

    base = [row(ex) for ex in rows]
    constants = tuple(constants)
    if len(base) != len(constants) or any(not 0 < c < field.size for c in constants):
        raise ValueError("invalid constants")
    polys, blocks = [], []
    for terms in polynomials:
        combined = {}
        for c,ex in terms:
            if type(c) is not int or not 0 <= c < field.size:
                raise ValueError("invalid coefficient")
            ex = row(ex)
            combined[ex] = combined.get(ex,0) ^ c
        poly = [(c,ex) for ex,c in combined.items() if c]
        polys.append(poly)
        blocks.append([tuple((a-b) % order for a,b in zip(ex,poly[0][1])) for _,ex in poly[1:]])

    nodes, seen = [], set()
    pending = [(tree,False)] if tree is not None or polys else []
    roots = []
    while pending:
        t, closing = pending.pop()
        if closing:
            right, left = roots.pop(), roots.pop()
            leaves, children = nodes[left][0] | nodes[right][0], (left,right)
        elif type(t) is int and 0 <= t < len(polys) and t not in seen:
            seen.add(t)
            leaves, children = frozenset([t]), ()
        elif isinstance(t,(tuple,list)) and len(t)==2:
            pending.extend(((t,True),(t[1],False),(t[0],False)))
            continue
        else:
            raise ValueError("invalid leaf or binary pair")
        roots.append(len(nodes))
        nodes.append((leaves,children))
    if len(seen) != len(polys):
        raise ValueError("missing leaves")
    if any(_monomial(field,constants,r)!=1 for r in _relations(order,n,base)) or any(not p for p in polys):
        return Decision("UNSAT",None,0)
    if not polys:
        return Decision("SAT",1,1)
    universe = frozenset(seen)
    initial = lattice_index(order,base,n)
    sizes = {}
    def image_size(leaves):
        if leaves not in sizes:
            rows = [ex for i in sorted(leaves) for ex in blocks[i]]
            sizes[leaves] = initial // lattice_index(order,base+rows,n)
        return sizes[leaves]

    joint = image_size(universe)
    cuts = [image_size(s)*image_size(universe-s)//joint for s,_ in nodes]
    width = max(cuts)
    if width > max_overlap:
        return Decision("UNKNOWN",width,0)

    indexed = [(i,ex) for i,block in enumerate(blocks) for ex in block]
    full = _relations(order,n,base+[ex for _,ex in indexed])
    tables, peak = [], 0
    for (leaves,children),cut in zip(nodes,cuts):
        # All cuts use the same ambient signature coordinates, including constants.
        pin_indices, pins, indices = {}, [], []
        for rel in full:
            active = [(a,ex) for a,(i,ex) in zip(rel[len(base):],indexed) if a and i in leaves]
            new = tuple(sum(a*ex[j] for a,ex in active) % order for j in range(n))
            if not any(new):
                indices.append(None)
                continue
            if new not in pin_indices:
                pin_indices[new] = len(pins)
                pins.append(new)
            indices.append(pin_indices[new])
        states = [()]
        for j,new in enumerate(pins):
            states = [v+(z,) for v in states for z in
                      _values(field,n,base+pins[:j],constants+v,new,cut)]
        if len(states) != cut:
            raise ArithmeticError("signature size differs from cut index")
        peak = max(peak,len(states))
        if not children:
            poly = polys[next(iter(leaves))]
            states = [v for v in states if _nonzero(field,base+pins,constants+v,poly)]
        allowed = {tuple(1 if j is None else v[j] for j in indices) for v in states}
        if children:
            left,right = (tables[j] for j in children)
            joined = set()
            for u in left:
                for v in right:
                    sig = tuple(field.mul(a,b) for a,b in zip(u,v))
                    if sig in allowed:
                        joined.add(sig)
            allowed = joined
        if not allowed:
            return Decision("UNSAT",width,peak)
        tables.append(allowed)
    return Decision("SAT",width,peak)
