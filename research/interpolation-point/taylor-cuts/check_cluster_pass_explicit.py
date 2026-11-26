"""Cross-check production certificates without using production closure decisions."""
from copy import deepcopy
from random import Random
from cluster_pass_certificate import produce
from cluster_pass_explicit_verifier import verify


def truth(n, d, passes, start, closing):
    for mask in range(1 << n):
        for s in range(d) if start is None else (start,):
            value = s
            for _, gates in passes:
                for lit, p, q in gates:
                    choice = (mask >> (abs(lit)-1)) & 1
                    value = (q if choice ^ (lit < 0) else p)[value]
            if closing[value] == s:
                return True
    return False


rng = Random(381577)
counts = [0, 0]
for trial in range(120):
    n, d = rng.randrange(4), rng.choice((2, 3))
    order = rng.sample(range(1, n+1), n)
    passes = []
    for _ in range(rng.randrange(4)):
        forward = rng.choice((True, False))
        gates = []
        for v in order if forward else reversed(order):
            for _ in range(rng.randrange(3)):
                gates.append((rng.choice((v, -v)), rng.sample(range(d), d), rng.sample(range(d), d)))
        passes.append((forward, gates))
    lengths = [1]*len(passes)
    if trial % 3 == 0 and len(lengths) >= 2:
        lengths = [2] + lengths[2:]
    closing = rng.sample(range(d), d)
    start = rng.choice([None, *range(d)])
    args = (n, d, passes, order, lengths)
    options = dict(closing=closing, start=start)
    cert = produce(*args, **options)
    decision = truth(n, d, passes, start, closing)
    assert decision == (cert[0] == "sat")
    counts[decision] += 1
    assert verify(*args, cert, **options)
    if decision:
        assert not verify(*args, ("sat", 1 << n, cert[2]), **options)
    elif lengths:
        bad = deepcopy(cert)
        bad[1][0][0] = []
        assert not verify(*args, bad, **options)

# The synchronized double toggle always cancels, while independent cluster prefixes
# at the final cut can disagree. Observable suffix closure there is nonvacuous.
ident, swap = [0, 1], [1, 0]
args = (1, 2, [(True, [(1, ident, swap)]), (False, [(1, ident, swap)])], [1], [1, 1])
valid = produce(*args, closing=swap)
assert valid[0] == "unsat" and valid[2][1] and verify(*args, valid, closing=swap)
bad = deepcopy(valid)
bad[2][1] = []
assert not verify(*args, bad, closing=swap)
bad = deepcopy(valid)
bad[2][1] = [1]
assert not verify(*args, bad, closing=swap)
bad = deepcopy(valid)
bad[1][1][0] = [0]
assert not verify(*args, bad, closing=swap)
assert not verify(*args, valid, closing=ident)
print(f"{counts[1]} SAT and {counts[0]} UNSAT certificates replayed; targeted closure and mask tampering rejected.")
