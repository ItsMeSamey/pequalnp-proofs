"""Certified state-affine AND banks with reachable physical basis histories."""



class _Skip(Exception):
    pass


def _indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def estimate(n, gates, output):
    """Dispatch hint in scalar work units; solve enforces its own hard counter."""
    return (1 + n + len(gates)) * (1 + len(gates))


def solve(n, gates, output, *, budget, banks=None, fresh=None, degree=2):
    """Optional banks are consecutive exclusive gate endpoints (before output).
    Optional fresh lists declare zero-based original input IDs per genuine bank.
    The constant-output comparison is compiled as a final, additional bank.
    """
    used = 0
    peak = 0
    checked = 0

    def spend(amount=1):
        nonlocal used
        if amount > budget - used:
            raise _Skip
        used += amount

    def result(status, witness=None):
        answer = dict(status=status, cost=dict(work=used, metric="symbolic and vector operations",
                                              peak_basis=peak, certified_banks=checked))
        if witness is not None:
            answer["witness"] = witness
        return answer

    try:
        if n < 0 or degree < 0 or budget <= 0:
            raise _Skip
        m = len(gates)
        spend(n + m + 1)
        ends = list(range(1, m+1)) if banks is None else list(banks)
        if (ends and (ends[-1] != m or ends[0] <= 0)) or (not ends and m):
            raise _Skip
        if any(a >= b for a,b in zip(ends,ends[1:])):
            raise _Skip
        if fresh is not None and len(fresh) != len(ends):
            raise _Skip
        operations = list(gates) + [(output, 1)]
        first = {}
        last = {}
        for j,(a,b) in enumerate(operations):
            if min(a,b) < 0 or (a|b).bit_length() > n+j+1:
                raise _Skip
            for wire in _indices((a|b) & ~1):
                spend()
                first.setdefault(wire,j)
                last[wire] = j
        # The final synthetic output wire must survive its defining operation.
        last[n+m+1] = m+1
        known = []
        histories = [(1,0)]  # bit zero is the augmented constant
        start = 0
        for layer,end in enumerate(ends+[m+1]):
            spend(n + end + len(known))
            inputs = [i for i in range(1,n+1) if start <= first.get(i,-1) < end]
            if fresh is not None and layer < len(ends):
                declared = list(fresh[layer])
                if sorted(declared) != [i-1 for i in inputs]:
                    return result("skip")
            state_count = len(known)
            state_mask = (1 << state_count)-1
            polys = {wire:{1 << i} for i,wire in enumerate(known+inputs)}

            def affine(mask):
                out = {0} if mask & 1 else set()
                for wire in _indices(mask & ~1):
                    terms = polys[wire]
                    spend(1+len(terms))
                    out.symmetric_difference_update(terms)
                return out

            for j in range(start,end):
                left,right = map(affine, operations[j])
                out = set()
                spend(1+len(left)*len(right))
                for x in left:
                    for y in right:
                        term=x|y
                        if term in out:
                            out.remove(term)
                        else:
                            out.add(term)
                if any((t&state_mask).bit_count()>1 or (t>>state_count).bit_count()>degree for t in out):
                    return result("skip")
                polys[n+j+1] = out
            live = [w for w in polys if last.get(w,-1)>=end]
            spend(1 + sum(len(polys[w]) for w in live))
            # Only fresh monomials appearing in a matrix coefficient are needed.
            # Include empty for the augmented constant and use zeta triangularity.
            settings = {0}
            for w in live:
                settings.update(t>>state_count for t in polys[w])
            pivots = {}
            next_histories = []
            for setting in sorted(settings):
                raw = 0
                for bit in _indices(setting):
                    spend()
                    raw |= 1 << (inputs[bit]-1)
                for vector,history in histories:
                    assignment = (vector>>1) | (setting<<state_count)
                    new = 1
                    for i,w in enumerate(live,1):
                        terms = polys[w]
                        spend(1+len(terms))
                        new |= (sum((assignment&t)==t for t in terms)%2)<<i
                    rem = new
                    while rem:
                        spend()
                        h = rem.bit_length()-1
                        if h not in pivots:
                            pivots[h]=rem
                            next_histories.append((new,history|raw))
                            break
                        rem ^= pivots[h]
            known,histories,start = live,next_histories,end
            checked += 1
            peak = max(peak,len(histories))
        for vector,word in histories:
            if vector & 2:
                # Replay the raw physical net, irrespective of the selected chart.
                values = 1 | (word<<1)
                for j,(a,b) in enumerate(gates):
                    spend()
                    gate = ((a&values).bit_count() & (b&values).bit_count() & 1)
                    values |= gate << (n+j+1)
                spend()
                if (values&output).bit_count()%2 != 1:
                    raise RuntimeError("reachable witness replay failed")
                return result("sat",word)
        return result("unsat")
    except _Skip:
        return result("skip")
