"""Small exhaustive reference checks for CNF order and table recognition."""
from itertools import permutations, product
from random import Random
from decode import decode
from fibers import solve


def table_checks():
    pairs = list(product(range(3), repeat=2))
    for mask in range(1 << len(pairs)):
        rel = {pair for i, pair in enumerate(pairs) if mask & (1 << i)}
        # Three corners of a rectangle imply the fourth.
        rectangular = all((a,y) in rel for a,b in rel for x,y in rel if (x,b) in rel)
        d = {0: range(3), 'vertex': range(3)}
        status, w = solve(d, [(0,'vertex',rel)])
        expected = 'unsat' if not rel else ('sat' if rectangular else 'unsupported')
        assert status == expected
        if w:
            assert (w[0], w['vertex']) in rel
    # Equal numbers of blocks can hide different partitions at one endpoint.
    edges = [(0,1,{(a,a//2) for a in range(4)}), (0,2,{(a,a%2) for a in range(4)})]
    for order in permutations(edges):
        assert solve({0:range(4),1:range(2),2:range(2)},order)[0] == 'unsupported'


def order_checks():
    rng = Random(193)
    for _ in range(300):
        scopes = [(1,5),(1,5,3),(3,2,4)]
        cnf = [[-v if b else v for v,b in zip(scope,bits)] for scope in scopes
               for bits in product((0,1),repeat=len(scope)) if rng.randrange(3)==0]
        truth = lambda w: all(any(bool(w[abs(l)]) == (l>0) for l in c) for c in cnf)
        oracle = any(truth(dict(enumerate(bits,1))) for bits in product((0,1),repeat=5))
        statuses = set()
        for i in range(5):
            rng.shuffle(cnf)
            for clause in cnf:
                rng.shuffle(clause)
            status, w = decode(cnf, rng.sample(range(1,7),6))
            statuses.add(status)
            if status != 'unsupported':
                assert (status == 'sat') == oracle
            if w is not None:
                assert truth(w) and 6 in w
        assert len(statuses) == 1


if __name__ == '__main__':
    for malformed in ([[0]], [[9, -9]]):
        try:
            decode(malformed, [1])
        except ValueError:
            pass
        else:
            raise AssertionError("malformed literals accepted")
    table_checks()
    order_checks()
    print('512 table masks, incompatible partitions, 1500 CNF orderings passed')
