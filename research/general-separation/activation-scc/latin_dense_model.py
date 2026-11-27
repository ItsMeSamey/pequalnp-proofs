"""Find dense false supports under one binary-group Latin block and signed stars."""
from itertools import combinations

def dense_model(q, sites, pins, excess):
    """Each site is (representative index, sign); physical truth is rep XOR sign."""
    if q < 1 or q & (q-1) or len(sites) != 3*q or excess < 1:
        raise ValueError("invalid group, site count or excess")
    if any(not 0 <= rep < 3*q or sign not in (0,1) for rep, sign in sites):
        raise ValueError("invalid representative or sign")
    pins = set(pins)
    if any(i < 0 or i >= len(sites) for i in pins):
        raise ValueError("invalid pin")
    if excess > q:
        return None
    n = max(rep for rep, _ in sites)+1
    counts = [[0,0] for _ in range(n)]
    for rep, sign in sites:
        counts[rep][sign] += 1

    def lift(allowed):
        fixed = {}
        for i,(rep,sign) in enumerate(sites):
            if i in pins or not (allowed[i//q] >> (i%q)) & 1:
                required = sign ^ 1
                if rep in fixed and fixed[rep] != required:
                    return None
                fixed[rep] = required
        bits = [fixed.get(j,int(c[1]>c[0])) for j,c in enumerate(counts)]
        if sum(c[b] for c,b in zip(counts,bits)) >= q+excess:
            physical = [bits[rep]^sign for rep,sign in sites]
            assert all(physical[i] for i in pins)
            assert physical.count(0) >= q+excess
            assert all(physical[i] or physical[q+j] or physical[2*q+(i^j)]
                       for i in range(q) for j in range(q))
            return bits
        return None

    full = (1<<q)-1
    for empty in range(3):
        allowed = [full]*3
        allowed[empty] = 0
        found = lift(allowed)
        if found is not None:
            return found
    for dim in range((q//excess).bit_length()):
        s = 1<<dim
        for basis in combinations(range(1,q),dim):
            chart = [sum(((r&v).bit_count()%2)<<i for i,r in enumerate(basis))
                     for v in range(q)]
            if len(set(chart)) != s:
                continue
            def expand(bits):
                return sum(((bits>>code)&1)<<v for v,code in enumerate(chart))
            for u in range(1,1<<s):
                for v in range(1,1<<s):
                    blocked = 0
                    for i in range(s):
                        if (u>>i)&1:
                            for j in range(s):
                                if (v>>j)&1:
                                    blocked |= 1<<(i^j)
                    w = ((1<<s)-1)^blocked
                    if w:
                        found = lift([expand(mask) for mask in (u,v,w)])
                        if found is not None:
                            return found
    return None
