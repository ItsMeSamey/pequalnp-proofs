"""Independent original-assignment oracle. All variable indices are zero based."""
from itertools import product
from math import prod
from random import Random

from read_two_ternary import evaluate


def direct(clauses, point):
    total = 0
    for bits in product((0, 1), repeat=len(point)):
        if all(any(bits[i] for i in clause) for clause in clauses):
            total += prod(p if bit else 1-p for p,bit in zip(point,bits))
    return total % 3


def main():
    fixtures = [
        (0, []), (0,[()]), (2,[]), (2,[(),(0,)]),
        (3,[(0,0,1),(0,1)]), (3,[(0,1),(1,2),(2,0)]),
        (4,[(0,1),(1,2),(2,3),(3,0)]),
        (5,[(0,1,2),(0,3),(1,3,4),(2,4)]),
        (4,[(0,0,0),(0,), (1,2)]),
    ]
    count = 0
    for n,clauses in fixtures:
        for point in product(range(3),repeat=n):
            assert evaluate(clauses,point) == direct(clauses,point)
            count += 1
    rng = Random(19031)
    for _ in range(80):
        n = rng.randrange(1,7)
        clauses = [[] for _ in range(rng.randrange(1,7))]
        for i in range(n):
            for j in rng.sample(range(len(clauses)),rng.randrange(min(2,len(clauses))+1)):
                clauses[j].extend([i]*(1+rng.randrange(2)))
        point = [rng.randrange(3) for _ in range(n)]
        assert evaluate(clauses,point) == direct(clauses,point)
        count += 1
    for clauses,point in [
        ([(0,),(0,),(0,)], [1]), ([(-1,)], [0]), ([(1,)], [1]),
        ([(False,)], [0]), ([(0.0,)], [0]), ([], [3]), ([], [-1]),
        ([], [True]), ([], [2.0]), ([(),(9,)], []),
    ]:
        try:
            evaluate(clauses,point)
        except ValueError:
            continue
        raise AssertionError((clauses,point))
    print(f'{count} original-cube comparisons and ten malformed inputs passed.')


if __name__ == '__main__':
    main()
