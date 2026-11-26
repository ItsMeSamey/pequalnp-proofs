from collections import defaultdict
from itertools import combinations, product
from random import Random


def satisfied(clause, assignment):
    return any(assignment[abs(lit)-1] == (lit > 0) for lit in clause)


def count(n, clauses):
    return sum(all(satisfied(c, a) for c in clauses) for a in product((False, True), repeat=n))


def frontier_count(n, short, wide):
    core = {abs(z) for c in short for z in c}
    last = {abs(z): i for i, c in enumerate(wide) for z in c}
    states = {frozenset(): 1}
    for i, clause in enumerate(wide):
        updated = defaultdict(int)
        pins = frozenset(-z for z in clause)
        reverse = {-z for z in pins}
        retire = {x for x in last if x not in core and last[x] == i}
        for state, weight in states.items():
            choices = [(state, weight)]
            if not state & reverse:
                choices.append((state | pins, -weight))
            for changed, coefficient in choices:
                projected = frozenset(z for z in changed if abs(z) not in retire)
                multiplier = 2 ** (len(retire) - len(changed) + len(projected))
                updated[projected] += multiplier * coefficient
        states = {s: w for s, w in updated.items() if w}
    total = 0
    for a in product((False, True), repeat=len(core)):
        assignment = dict(zip(sorted(core), a))
        if all(any(assignment[abs(z)] == (z > 0) for z in c) for c in short):
            for state, weight in states.items():
                if all(assignment[abs(z)] == (z > 0) for z in state):
                    total += weight
    return total * 2**(n-len(core | set(last)))


def check_embedding(n, core):
    s = n + 1
    guard = tuple(range(n + 2, n + 2 + (n - 1).bit_length()))
    variables = tuple(range(1, n + 1))
    short = [(-s,) + c for c in core]
    short.extend(c for y in guard for c in [(-s, y), (s, -y)])
    p = [guard + pair for pair in combinations(variables, 2)]
    neg = [(s,) + tuple(-j for j in variables if j != i) for i in variables]
    assert frontier_count(guard[-1], short, p + neg) == count(n, core)
    for assignment in product((False, True), repeat=n):
        missing = assignment.count(False)
        if missing in (1, 2):
            a = assignment + (False,) * (len(guard) + 1)
            assert sum(not satisfied(c, a) for c in p + neg) == 1
            assert all(satisfied(c, a) for c in short)


if __name__ == '__main__':
    rng = Random(1059)
    for _ in range(1000):
        n = rng.randrange(1, 8)
        def clause():
            return tuple(x*rng.choice((-1, 1)) for x in rng.sample(range(1, n+1), rng.randrange(1, n+1)))
        short = [clause() for _ in range(rng.randrange(7))]
        wide = [clause() for _ in range(rng.randrange(11))]
        assert frontier_count(n, short, wide) == count(n, short+wide)
    for n in range(3, 9):
        for _ in range(15):
            core = [tuple(x*rng.choice((-1, 1)) for x in rng.sample(range(1,n+1),3)) for _ in range(n)]
            check_embedding(n, core)
    print('1000 random signed-frontier comparisons and 90 parsimonious embeddings passed.')
