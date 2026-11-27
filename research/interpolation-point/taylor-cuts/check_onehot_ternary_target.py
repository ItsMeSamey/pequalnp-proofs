from itertools import combinations, product
from random import Random
from check_onehot_colour_folds import encode
from onehot_ternary_target import decide


def main():
    rng = Random(288)
    fixtures = 0
    for n in range(5):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [edge for j, edge in enumerate(possible) if mask >> j & 1]
            clauses, equations = encode(n, edges, rng)
            expected = any(all(word[a] != word[b] for a, b in edges)
                           for word in product(range(3), repeat=n))
            status, witness, _ = decide(3*n, clauses, equations, state_cap=10000)
            assert (status, witness is not None) == (("SAT", True) if expected else ("UNSAT", False))
            fixtures += 1
    print(fixtures, "signed/permuted source decisions")
if __name__ == "__main__":
    main()
