from random import Random
from unittest import TestCase, main

from signed_cuts import count_assignments


class SignedCutsTests(TestCase):
    def test_boundaries(self):
        for clauses, n, expected in [
            ([], 0, 1), ([[]], 2, 0), ([[(0, 1)]], 3, 8),
            ([[(0, 0)]], 0, 0), ([[(1, 0)], [(1, 1)]], 2, 0),
            ([[(3, 1)]] * 5, 3, 4)
        ]:
            self.assertEqual(count_assignments(clauses, n), expected)

    def test_random(self):
        rng = Random(852)
        for _ in range(1200):
            n = rng.randrange(8)
            clauses = [[(rng.randrange(1 << n), rng.randrange(2))
                        for _ in range(rng.randrange(1, 4))]
                       for _ in range(rng.randrange(8))]
            expected = sum(all(any(((mask & x).bit_count() & 1) != rhs
                                   for mask, rhs in clause)
                               for clause in clauses) for x in range(1 << n))
            self.assertEqual(count_assignments(clauses, n), expected)


if __name__ == "__main__":
    main()
