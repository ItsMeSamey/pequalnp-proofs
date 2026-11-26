"""Independent subspace enumeration and direct assignment comparisons."""
from random import Random
from backdoor import minimum_forms, compile_projection, witness


def enlarge(space, row):
    return space | frozenset(x ^ row for x in space)


def spaces(n):
    result = {frozenset([0])}
    for i in range(n):
        result |= {enlarge(s, x) for s in result for x in range(1 << n)}
    return result


def check():
    rng = Random(17893)
    observations = 0
    for ny in range(6):
        family = spaces(ny)
        for _ in range(80):
            nx = rng.randrange(4)
            def form():
                return rng.randrange(1 << ny), rng.randrange(2 << nx)
            rows = [form() for _ in range(rng.randrange(3))]
            clauses = [[form() for _ in range(rng.randrange(5))]
                       for _ in range(rng.randrange(6))]
            base = frozenset([0])
            for mask, _ in rows:
                base = enlarge(base, mask)
            def valid(s):
                return all(len({min(m ^ h for h in s) for m, _ in clause} - {0}) <= 1
                           for clause in clauses)
            optimum = min(len(s) for s in family if base <= s and valid(s))
            found = base
            for mask in minimum_forms(rows, clauses):
                found = enlarge(found, mask)
            assert valid(found) and len(found) == optimum
            circuit, root = compile_projection(nx, ny, rows, clauses)
            for x in range(1 << nx):
                def accepts(y):
                    def value(f):
                        m, a = f
                        return ((m & y).bit_count() + (a & (x | 1 << nx)).bit_count()) % 2
                    return not any(map(value, rows)) and all(any(map(value, c)) for c in clauses)
                models = {y for y in range(1 << ny) if accepts(y)}
                answer = witness(nx, ny, rows, clauses, x)
                assert bool(circuit.evaluate(root, x)) == bool(models)
                assert (answer in models) if models else (answer is None)
                observations += 1
    print(f"480 minimum-dimension checks and {observations} projection/witness checks passed")


if __name__ == "__main__":
    check()
