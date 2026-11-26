"""Pinned equality on one private coordinate per clause; independent small controls."""
from itertools import combinations, product
from random import Random


def evaluate(colors, word):
    value = 0
    while word:
        low = word & -word
        value ^= colors[low.bit_length()-1]
        word ^= low
    return value


def private_witness(domains, clauses, pins):
    """Return variable and clause values giving the specified transversal basis."""
    if any(not domain for domain in domains) or any(not row for row in clauses):
        return None
    n = len(domains)
    defaults = [domain[0] for domain in domains]
    for count in range(min(2*len(pins), n)+1):
        for changed in combinations(range(n), count):
            for replacements in product(*(domains[i][1:] for i in changed)):
                variables = defaults.copy()
                for i, color in zip(changed, replacements):
                    variables[i] = color
                target = 0
                for j, (word, value) in enumerate(pins):
                    target |= (value ^ evaluate(variables, word & ((1<<n)-1))) << (2*j)
                reachable = {0: ()}
                for t, alternatives in enumerate(clauses):
                    choices = {offset ^ evaluate(variables, word) for word, offset in alternatives}
                    next_states = {}
                    for score, used in reachable.items():
                        for value in choices:
                            delta = sum((value if word>>(n+t)&1 else 0) << (2*j)
                                        for j, (word, _) in enumerate(pins))
                            next_states.setdefault(score ^ delta, used + (value,))
                    reachable = next_states
                if target in reachable:
                    return tuple(variables) + reachable[target]
    return None


def valid(colors, domains, clauses, pins):
    n = len(domains)
    return (all(colors[i] in domain for i,domain in enumerate(domains))
            and all(any(colors[n+j] ^ evaluate(colors, word) == value for word,value in row)
                    for j,row in enumerate(clauses))
            and all(evaluate(colors,word)==value for word,value in pins))


def main():
    rng = Random(318)
    hits = 0
    for run in range(250):
        n, m = rng.randrange(4), rng.randrange(4)
        domains = [tuple(range(4)) if run%2 else tuple(sorted(rng.sample(range(4),rng.randrange(1,5)))) for _ in range(n)]
        clauses = [[(rng.randrange(1<<n),rng.randrange(4)) for _ in range(rng.randrange(1,4))]
                   for _ in range(m)]
        pins = [(rng.randrange(1<<(n+m)),rng.randrange(4)) for _ in range(2)]
        ans = private_witness(domains,clauses,pins)
        brute = next((z for z in product(range(4),repeat=n+m) if valid(z,domains,clauses,pins)),None)
        assert (ans is not None)==(brute is not None)
        if ans is not None:
            hits+=1
            assert valid(ans,domains,clauses,pins)
    print('250 dense two-pin cases;',hits,'YES')
    # Four independent changes are necessary for these two four-bit aggregate equations.
    domains = [(0,1),(0,2),(0,1),(0,2)]
    pins = [(3,3),(12,3)]
    assert private_witness(domains, [], pins)==(1,2,1,2)
    print('four-exception threshold attained')


if __name__ == '__main__':
    main()
