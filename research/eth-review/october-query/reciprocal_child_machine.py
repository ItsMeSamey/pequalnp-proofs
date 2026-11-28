"""Reciprocal-mode sample and full supplied-root dispatch, using frozen birth entries."""
from one_packet_layer import Ring, interpolate, recover, unit_inverse
from tapered_jet_machine import valuation
from two_sided_cauchy_modes import column_mode, mode_weight, native_entries, target_modes
from variable_packet_machine_affine import Description, solve as ordinary_solve


def sample(network, packets, labels, t, zeta, ring, evaluate, *, visit=None):
    """evaluate(child, edge_count, birth_ring) must return one contraction at birth.

    visit(beta, child_group, child) is optional; beta is a sparse immutable tuple.
    Returns (scalar, counters). Input is one source-legal shell labelling.
    """
    packets = tuple(tuple(q) for q in packets)
    length = len(packets[0])
    slots = [e for q in packets for e in q if e is not None]
    if len(slots) != len(set(slots)) or any(len(q) != length for q in packets):
        raise ValueError("invalid packet partition")
    owners = []
    for vertices, side in zip(network, labels, strict=True):
        pairs = [(e,g) for (_,edges),g in zip(vertices,side,strict=True) for e in edges]
        if len(pairs) != len(slots) or {e for e,_ in pairs} != set(slots):
            raise ValueError("packet ports must match each shore")
        owners.append(dict(pairs))
    groups = sorted(set(labels[0]) | set(labels[1]))
    zero, one = ring.scalar(0), ring.scalar(1)
    level = valuation(t)
    step = 2 << level
    ops = dict(one=one, add=ring.add, mul=ring.mul,
               scale=lambda a,n: ring.mul(a,ring.scalar(n)),
               inverse_unit=lambda a:unit_inverse(ring,a))
    weight, crossing = native_entries(length,t,zeta,ring.p,**ops)
    modes = []
    coeff = {}
    moments = {}
    costs = {}
    capacities = {}
    local = {}
    for p,q in enumerate(packets):
        real = [x for x,e in enumerate(q) if e is not None]
        for g in groups:
            rows,cols = tuple([x for x in real if owners[side][q[x]] == g] for side in (0,1))
            local[p,g] = rows,cols,tuple(tuple(weight(x,y) for y in cols) for x in rows)
            capacities[p,g] = len(rows)
        for y0 in range(step):
            cols = [y for y in real if y % step == y0]
            if not cols:
                continue
            source = owners[1][q[cols[0]]]
            if any(owners[1][q[y]] != source for y in cols):
                raise ValueError("mixed source label in residue tile")
            limit = 1+(cols[-1]-y0)//step
            for g in groups:
                if g == source:
                    continue
                tile = {}
                for x in local[p,g][0]:
                    for k,c in target_modes(*crossing(x,y0),limit,ring.p,**ops):
                        if c != zero:
                            tile.setdefault(k,{})[x] = c
                for k,values in sorted(tile.items()):
                    z = (p,source,g,y0,k)
                    ws = {y:column_mode((y-y0)//step,k,ring.p) for y in cols}
                    w = length.bit_length()-1-level + mode_weight(k)
                    if any(ws.values()) and w < ring.p:
                        modes.append(z)
                        coeff[z], moments[z], costs[z] = values,ws,w
    # Enumerate nonzero sparse exponent vectors, increasing their final index
    # (repeat that index to increase its exponent). Each vector has one parent.
    total = zero
    counts = dict(modes=len(modes), tuples=0, children=0)
    beta = {}
    used = {}
    def consume():
        nonlocal total
        value = one
        for g in groups:
            names,old,new = {},[],[]
            for side in (0,1):
                for (desc,edges),owner in zip(network[side],labels[side],strict=True):
                    if owner == g:
                        ids = []
                        for e in edges:
                            names[side,e] = len(names)
                            ids.append(names[side,e])
                        old.append((desc,tuple(ids)))
            for p,q in enumerate(packets):
                rows,cols,base = local[p,g]
                if not rows and not cols:
                    continue
                tar = [z for z in beta if z[0] == p and z[2] == g]
                src = [z for z in beta if z[0] == p and z[1] == g]
                affine = tuple((v,tuple((j,coeff[z][x]) for j,z in enumerate(tar) if x in coeff[z]))
                               for x,v in zip(rows,base,strict=True))
                born = Description(ring,affine,len(cols),tuple(beta[z] for z in tar),
                                   tuple((tuple(moments[z].get(y,0) for y in cols),beta[z]) for z in src))
                edges = tuple(names[side,q[x]] for side,sites in enumerate((rows,cols)) for x in sites)
                new.append((born,edges))
            child = (old,new)
            if visit is not None:
                visit(tuple(beta.items()),g,child)
            value = ring.mul(value,evaluate(child,len(names),ring))
            counts["children"] += 1
        total = ring.add(total,value)
        counts["tuples"] += 1
    consume()
    stack = [[0,ring.p-1,None]]
    while stack:
        j,left,last = stack[-1]
        if j == len(modes):
            stack.pop()
            if last is not None:
                bucket = last[0],last[2]
                used[bucket] -= 1
                beta[last] -= 1
                if not beta[last]:
                    del beta[last]
            continue
        stack[-1][0] += 1
        z = modes[j]
        bucket = z[0],z[2]
        if costs[z] > left or used.get(bucket,0) == capacities[bucket]:
            continue
        used[bucket] = used.get(bucket,0)+1
        beta[z] = beta.get(z,0)+1
        consume()
        stack.append([j,left-costs[z],z])
    return total,counts


def solve_root(network,m,p,f,ell,spec,*,evaluate=None):
    """Full root schedule at original precision; scalar callback may recurse separately."""
    a,u,packets,labels = spec
    length = 1 << a
    if not (1 <= u <= min(m,a)) or any(len(q)!=length for q in packets):
        raise ValueError("invalid supplied active root")
    degree = m*(2*length-1)
    if degree+1 > 1 << len(f):
        raise ValueError("insufficient interpolation field")
    if evaluate is None:
        def evaluate(child,n,r):
            return ordinary_solve(child,n,r.p,r.f,r.ell,0,lambda *_:None)
    h = (3*m+u-1)//u
    jets = {}
    for t in range(-length,length):
        if not t or valuation(t)>=u:
            continue
        i = valuation(t)
        ring = Ring(p+8*h*(length>>i)+8*m*(a+1),f,ell)
        points = [tuple((j>>b)&1 for b in range(len(f)))+(0,)*(len(f)*(ell-1))
                  for j in range(degree+1)]
        values = [sample(network,packets,labels[i],t,zeta,ring,evaluate)[0] for zeta in points]
        jets[t] = interpolate(ring,points,values)[:h*(u-i)]
    return tuple(recover(a,u,m,p,len(f)*ell,lambda t,j,c,prec:jets[t][j][c]))
