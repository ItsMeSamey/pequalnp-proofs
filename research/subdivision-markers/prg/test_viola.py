from collections import Counter
from functools import reduce
from itertools import product
from operator import xor
import unittest

from viola import block, field_degree, field_modulus, find_target, multiply, sample


class GeneratorTests(unittest.TestCase):
    def test_field(self):
        for ell in range(1, 7):
            m = field_modulus(ell)
            q = 1 << ell
            for a in range(1, q):
                self.assertEqual({multiply(a, b, m) for b in range(q)}, set(range(q)))
                for b in range(q):
                    self.assertEqual(multiply(a,b,m), multiply(b,a,m))

    def test_linear(self):
        n, ell = 5, 3
        q = 1 << ell
        m = field_modulus(ell)
        for mask in range(1, 1 << n):
            roots = 0
            for a in range(q):
                value = 0
                for j in reversed(range(n)):
                    value = multiply(value, a, m) ^ ((mask >> j) & 1)
                roots += (value == 0)
            signs = sum((-1)**((block(n,a,b,m) & mask).bit_count() % 2)
                        for a,b in product(range(q), repeat=2))
            self.assertEqual(signs, q*roots)
            self.assertLessEqual(roots, n-1)

    def test_quadratic(self):
        n, d, ell = 3, 2, 2
        single = [sample(n,1,ell,k) for k in range(1 << (2*ell))]
        counts = Counter(sample(n,d,ell,k) for k in range(1 << (2*d*ell)))
        self.assertEqual(counts, Counter(a ^ b for a,b in product(single, repeat=2)))
        worst = 0
        monomials = [m for m in range(1,8) if m.bit_count() <= 2]
        for terms in range(1 << len(monomials)):
            signs = [(-1)**(sum(bool(terms >> j & 1) and x & m == m
                                 for j,m in enumerate(monomials)) % 2) for x in range(8)]
            diff = sum((counts[x]-32)*signs[x] for x in range(8))
            worst = max(worst, abs(diff))
        self.assertEqual(worst, 64)  # exact max sign error 64/256

    def test_graph(self):
        # One triangle (cycle bit 0), plus one isolated vertex (seed bit 4).
        # Inactive triangle vertices use independent isolate seeds, bits 1..3.
        adjacency = [6,5,3,0]
        labels = [1,2,4,8]
        def evaluate(x):
            active = 7 if x & 1 else 0
            y = x >> 1
            selected = active
            for v, neighbors in enumerate(adjacency):
                if y >> v & 1 and not (neighbors & (active | y)):
                    selected |= 1 << v
            return reduce(xor,(labels[v] for v in range(4) if selected >> v & 1),0), selected
        x, witness = find_target(5,4,4,15,evaluate)
        self.assertEqual(evaluate(x),(15,witness))
        self.assertEqual(witness,15)
        self.assertIsNone(find_target(5,4,4,3,evaluate))
        # Explicit seed hit yielding the cycle plus its isolated vertex.
        x = sample(5,4,2,5)  # first block has a=b=1
        self.assertEqual(evaluate(x),(15,15))
        self.assertTrue(all((neighbors & witness).bit_count()%2 == 0 for neighbors in adjacency))

    def test_certified_prg_branch(self):
        # 40 > seed length 24, so this takes the certified PRG branch.
        self.assertEqual(field_degree(40,1,1),12)
        self.assertEqual(find_target(40,1,1,1,lambda x:(x&1,x)),(1,1))


if __name__ == '__main__':
    unittest.main()
