from fractions import Fraction
from itertools import combinations, product
from random import Random

rng = Random(22098)
accepted = 0
def ok(clause, assignment):
    return len({((assignment >> x) & 1) ^ s for x, s in clause}) == 2

for case in range(401):
    n = rng.randrange(3, 6)
    clauses = []
    for _ in range(rng.randrange(1, 6)):
        variables = rng.sample(range(n), rng.choice((2,3)))
        clauses.append([(x,rng.randrange(2)) for x in variables])
    if case == 0:
        n = 4
        clauses = [[(0,0),(1,1),(2,0)],[(0,0),(2,0),(3,0)],[(0,0),(3,0),(1,0)]]
    options = []
    for clause in clauses:
        options.append([()] + list(combinations(range(len(clause)), 2)))
    bad = set()
    scalar = 0
    for selected in product(*options):
        parity = phase = mask = shift = 0
        idle = 1
        for clause, pair in zip(clauses, selected):
            if pair:
                phase ^= 1
                for j in pair:
                    x, sign = clause[j]
                    phase ^= sign
                    parity ^= 1 << x
                    mask |= 1 << (shift+j)
            elif len(clause) == 3:
                idle *= 3
            shift += len(clause)
        if not parity:
            scalar += (-1 if phase else 1) * idle
            if phase:
                bad.add(mask)
    assignments = list(range(1<<n))
    count = sum(all(ok(c,a) for c in clauses) for a in assignments)
    assert Fraction(count,2**n) == Fraction(scalar,2**sum(len(c)-1 for c in clauses))
    if any((x^y) in bad for x in bad for y in bad):
        continue
    accepted += 1
    binary = [c for c in clauses if len(c)==2]
    candidates = [a for a in assignments if all(ok(c,a) for c in binary)]
    ternary = [c for c in clauses if len(c)==3]
    assert Fraction(count,1) >= Fraction(len(candidates),2**len(ternary))
    if not candidates:
        assert not count
        continue
    def verify_branches(i, current):
        if i == len(ternary):
            assert all(all(ok(c,a) for c in clauses) for a in current)
            return
        successors = [[a for a in current if ok(pair,a)] for pair in combinations(ternary[i],2)]
        assert any(successors)
        for nxt in successors:
            if nxt:
                verify_branches(i+1,nxt)
    verify_branches(0,candidates)
print(f'401 exact counts; all compatible greedy paths verified in {accepted} certified inputs')
