"""Source-word regression for paired signed comparisons; run via the 04 queue."""
from itertools import product
from random import Random

from balanced_block import UnsupportedBlock, balanced_block_witness, comparison_witness
from branch_block import branch_block_witness, branch_comparison_witness


def comparisons_hold(bits, edges):
    valid = [(bits[a] ^ bits[b]) == d for a, b, d in edges]
    return all(valid[j] or valid[j+1] for j in range(0, len(edges), 2))


def raw_holds(bits, pins):
    return all((bits[a] ^ bits[b]) == d for a, b, d in pins) and all(
        bits[i:i+2] != bits[i+2:i+4] for i in range(0, len(bits), 4))


def brute(n, predicate):
    return any(predicate(bits) for bits in product((0, 1), repeat=n))


def check_result(result, n, predicate, exists):
    assert (result is not None) == exists
    if result is not None:
        assert len(result) == n and all(b in (0, 1) for b in result)
        assert predicate(tuple(result))


def to_raw(edges):
    first = {}
    pins = []
    for e, (a, b, d) in enumerate(edges):
        i = 4 * (e//2) + e%2
        for name, site, offset in ((a, i, 0), (b, i+2, 1^d)):
            old_site, old_offset = first.setdefault(name, (site, offset))
            if old_site != site:
                pins.append((old_site, site, old_offset ^ offset))
    return pins


def eligible(n, edges):
    """Recognize the comparison class by all connected degree-two edge subsets."""
    cycles = []
    for mask in range(1, 1 << len(edges)):
        degree = [0]*n
        adj = [set() for _ in range(n)]
        parity = 0
        for e,(a,b,d) in enumerate(edges):
            if mask >> e & 1:
                degree[a] += 1
                degree[b] += 1
                adj[a].add(b)
                adj[b].add(a)
                parity ^= d
        active = {j for j,deg in enumerate(degree) if deg}
        if any(degree[j] != 2 for j in active):
            continue
        stack = [next(iter(active))]
        reached = set(stack)
        while stack:
            fresh = adj[stack.pop()] - reached
            reached.update(fresh)
            stack.extend(fresh)
        if reached == active:
            cycles.append((mask,parity))
    return all(not (m & other) for m,odd in cycles if odd
               for other,_ in cycles if m != other)


def case(n, edges, physical):
    pred = lambda bits: comparisons_hold(bits, edges)
    exists = brute(n, pred)
    allowed = eligible(n, edges)
    check_result(branch_comparison_witness(n, edges), n, pred, exists)
    checks = [(comparison_witness, (n, edges), n, pred)]
    if physical:
        pins = to_raw(edges)
        count = 2*len(edges)
        pred_raw = lambda bits: raw_holds(bits, pins)
        assert brute(count, pred_raw) == exists
        check_result(branch_block_witness(count//4, pins), count, pred_raw, exists)
        checks.append((balanced_block_witness, (count//4, pins), count, pred_raw))
    for solver, args, count, test in checks:
        try:
            result = solver(*args)
        except UnsupportedBlock:
            assert not allowed
        else:
            assert allowed
            check_result(result, count, test, exists)
    return allowed, exists


def main():
    theta = [(0,1,0),(0,2,0),(2,1,0),(0,3,0),(3,1,1)]
    cases = [(0,[]), (1,[(0,0,1),(0,0,1)]),
             (2,[(0,1,0),(0,1,0),(0,1,1),(0,1,1)]),
             (4,theta+[(2,2,0)]), (4,theta[:4]+[(3,1,0),(2,2,0)]),
             (4,[(0,1,0),(2,3,1),(0,1,1),(2,3,0)]),
             (3,[(0,0,1),(1,1,1)]+[(0,1,d) for d in (0,1,0,1)])]
    rng = Random(1431)
    tally = {}
    for i in range(103):
        if i < len(cases):
            n, edges = cases[i]
        else:
            n = rng.randrange(1,6)
            edges = [(rng.randrange(n),rng.randrange(n),rng.randrange(2))
                     for _ in range(2*rng.randrange(1,4))]
        key = case(n, edges, i < len(cases) or len(edges) <= 4)
        tally[key] = tally.get(key,0)+1
    assert len(tally) == 4
    for solver in (balanced_block_witness, branch_block_witness):
        assert solver(1, [(0,1,1),(0,1,0)]) is None
    print('103 graph cases checked; (supported, satisfiable) counts:', sorted(tally.items()))


if __name__ == '__main__':
    main()
