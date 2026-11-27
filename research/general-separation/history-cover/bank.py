"""Automatic inter-stage parity summaries for raw or earlier-summary producer operands."""
from cover import System, compile_system, conflicts, search_cover


def compress(n, gates, out, cover_budget, stages=1):
    """Greedily summarize maximal input-only prefixes on the current circuit."""
    if min(stages, cover_budget) < 0:
        raise ValueError('negative budget')
    original_n = n
    definitions = []
    stats = {'banks': [], 'nodes': 0}
    gates = list(gates)
    for _ in range(stages):
        raw_mask = (1 << (n+1)) - 1
        k = 0
        for gate in gates:
            if any(row & ~raw_mask for row in gate):
                break
            k += 1
        if not k:
            break
        prefix_mask = (1 << k) - 1
        def prefix(row):
            return (row >> (n+1)) & prefix_mask

        # Pivot rows store residual vectors themselves as the formal summaries.
        pivots = {}
        for row in [r for gate in gates[k:] for r in gate] + [out]:
            vec = prefix(row)
            while vec:
                p = vec.bit_length()-1
                if p not in pivots:
                    pivots[p] = (vec, 1 << (n+1+len(pivots)))
                    break
                vec ^= pivots[p][0]

        def rewrite(row):
            vec = prefix(row)
            result = row & raw_mask
            while vec:
                v, symbol = pivots[vec.bit_length()-1]
                result ^= symbol
                vec ^= v
            return result | ((row >> (n+1+k)) << (n+1+len(pivots)))

        terms = 0
        for vec, symbol in pivots.values():
            poly = []
            for j in range(k):
                if vec >> j & 1:
                    u,v,w = gates[j]
                    poly.extend([(u,v),(w,)])
            definitions.append((symbol,poly))
            terms += len(poly)
        stats['banks'].append((k,len(pivots),terms))
        gates = [tuple(rewrite(r) for r in gate) for gate in gates[k:]]
        out = rewrite(out)
        n += len(pivots)
    edges = conflicts(n,gates,out)
    S = search_cover(edges,cover_budget,stats)
    if S is None:
        return None,stats
    suffix = compile_system(n,gates,out,S)
    stats['cover'] = sorted(S)
    return System(original_n,definitions+suffix.definitions,suffix.final),stats
