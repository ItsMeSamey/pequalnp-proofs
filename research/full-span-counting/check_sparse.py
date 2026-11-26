"""Exact sparse-support search with at most s+1 conflict rows and relative closures."""
from itertools import combinations
from random import Random
from sympy import Matrix, zeros, ones


def matrix(rows, cols):
    if not cols:
        return zeros(len(rows), 0)
    return Matrix([[int(u & v == v) for v in cols] for u in rows])


def consistent(rows, cols):
    a = matrix(rows, cols)
    return a.rank() == a.row_join(ones(len(rows), 1)).rank()


def find(rows, k):
    rows = [u for u in rows if u]
    def moment(s):
        return sum(u & s == s for u in rows)
    def local_columns(p):
        def closure(s):
            return sum(1<<i for i in range(p.bit_length())
                       if p >> i & 1 and moment(s) == moment(s | (1<<i)))
        start = closure(0)
        result, queue = {start}, [start]
        for a in queue:
            for i in range(p.bit_length()):
                if p >> i & 1 and not a >> i & 1:
                    nxt = closure(a | (1<<i))
                    if nxt not in result:
                        result.add(nxt)
                        queue.append(nxt)
        return result - {0}

    def recurse(cols):
        if consistent(rows, cols):
            return cols
        if len(cols) == k:
            return None
        witness = []
        for u in rows:
            if not consistent(witness+[u], cols):
                witness.append(u)
                break
            if matrix(witness+[u], cols).rank() > len(witness):
                witness.append(u)
        assert len(witness) <= len(cols)+1 and not consistent(witness, cols)
        old_rank = matrix(witness, cols).rank()
        candidates = set().union(*(local_columns(p) for p in witness))
        for s in sorted(candidates - set(cols)):
            if matrix(witness, cols+[s]).rank() > old_rank:
                solution = recurse(cols+[s])
                if solution is not None:
                    return solution
        return None
    return recurse([])


def main():
    rng = Random(9305)
    cases = 0
    for m in range(1,4):
        universe = list(range(1,1<<m))
        for _ in range(12):
            rows = [u for u in universe if rng.randrange(2)]
            rng.shuffle(rows)
            for k in range(4):
                result = find(rows, k)
                predicted = any(consistent(rows, cols) for j in range(k+1)
                                for cols in combinations(universe,j))
                assert (result is not None) == predicted
                if result is not None:
                    assert len(result) <= k and consistent(rows, result)
                cases += 1
    print(f"{cases} sparsity budgets checked against full brute-force support selection.")


if __name__ == '__main__':
    main()
