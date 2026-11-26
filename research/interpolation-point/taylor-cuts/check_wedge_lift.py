"""Independent exhaustive checks for the binary exterior-square lift."""
from itertools import combinations
from functools import reduce
from operator import xor


def span(vectors):
    out = {0}
    for v in vectors:
        out |= {z ^ v for z in out}
    return out


def wedge(a, b, d):
    pairs = combinations(range(d), 2)
    return sum(((((a >> i) & (b >> j)) ^ ((a >> j) & (b >> i))) & 1) << k
               for k, (i, j) in enumerate(pairs))


def dot(a, x):
    return (a & x).bit_count() & 1


def product_lift(u, v, chosen, use, x):
    # Polar parts cancel. The surviving linear term is the diagonal.
    diagonal = u & v
    for i in use:
        a, b = chosen[i]
        diagonal ^= a & b
    return dot(diagonal, x) ^ reduce(xor, (dot(chosen[i][0], x) *
                                           dot(chosen[i][1], x) for i in use), 0)


def main():
    d = 4
    vectors = range(1, 1 << d)
    spaces = {tuple(sorted(span(triple))) for triple in combinations(vectors, 3)}
    spaces = [set(v) for v in spaces if len(v) == 8]
    assert len(spaces) == 15
    for space in spaces:
        images = {wedge(a, b, d) for a, b in combinations(space-{0}, 2)}
        assert len(images) == 7 and len(span(images)) == 8 and 0 not in images
    for a in (0, 1):
        for b in (0, 1):
            for y in (0, 1):
                assert (y == (a & b)) == ((a or not y) and (not a or y == b))

    # A decomposable wedge represented via two generators, with nonzero diagonal correction.
    chosen = [(0b0011, 0b0110), (0b1011, 0b0110)]
    u, v = 0b1000 ^ 0b0110, 0b0110
    assert wedge(u, v, d) == wedge(*chosen[0], d) ^ wedge(*chosen[1], d)
    w = 1
    assert len(span([u,v,w])) == 8
    checks = 0
    for beta in range(8):
        for x in range(1<<d):
            a, b, c = (dot(h, x) for h in (u,v,w))
            # Delta factors 1+[actual]+[wanted] over GF(2).
            e, f = (1 ^ ((beta>>i)&1) for i in range(2))
            match_pair = product_lift(u,v,chosen,(0,1),x) ^ (a*f) ^ (b*e) ^ (e*f)
            assert match_pair == ((a == (beta&1)) and (b == ((beta>>1)&1)))
            forbidden = (match_pair == 1 and c == ((beta>>2)&1))
            assert forbidden == (a + 2*b + 4*c == beta)
            checks += 1

    # Seven lines of the Fano plane give seven triples with pairwise disjoint pair coordinates.
    triples = {tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,8),2)}
    subspaces = [span([wedge(1<<(a-1),1<<(b-1),7) for a,b in combinations(E,2)])
                 for E in triples]
    assert len(subspaces) == 7
    support_masks = [reduce(int.__or__, E) for E in subspaces]
    assert all(a & b == 0 for a,b in combinations(support_masks,2))
    print(f"{len(spaces)} rank-three spaces, {checks} affine tests, {len(subspaces)} disjoint Fano wedge spaces")


if __name__ == "__main__":
    main()
