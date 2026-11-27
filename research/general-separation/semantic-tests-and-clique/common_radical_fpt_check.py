"""Raw private kernels, their exact cubes, and a partial-chart missing-point control."""
from itertools import product
from diagonal_pin_cube_check import mv, reduce_rows
from minimal_singular_search_check import Field, minor, stream


def verify_private(A):
    n = len(A)
    vectors = [w for w in range(8,1 << n,8) if mv(A,w) & ~w == 0]
    direct_union = set()
    for exterior in range(1 << (n-3)):
        d = exterior << 3
        rows = [row ^ (d & (1 << i)) for i,row in enumerate(A)]
        # Substitute zero at each of the three pins in the complete kernel system.
        nullity = n-3-len(reduce_rows([row >> 3 for row in rows]))
        direct = {w for w in range(8,1 << n,8) if mv(rows,w) == 0}
        predicted = {w for w in vectors if not (d ^ mv(A,w)) & w}
        assert predicted == direct and len(direct)+1 == 1 << nullity
        direct_union |= direct
    assert direct_union == set(vectors)
    return len(reduce_rows(vectors)), vectors


def chart_control():
    F = Field(2,3)
    # Mandatory singleton {0} is singular. Arc 0--1 makes its two-site
    # extension feasible. Sites 2 and 3 are isolated unit diagonals.
    A = [[0,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]]
    for translation in (0,5):
        def missing_under(cube):
            required, forbidden = 1,0
            for j,b in enumerate(cube):
                if b is None:
                    continue
                if b ^ (translation >> j & 1):
                    required |= 2 << j
                else:
                    forbidden |= 2 << j
            return {(s >> 1) ^ translation for s in stream(A,required,forbidden,F)}
        raw = {x for x in range(8) if not minor(A,[0]+[1+j for j in range(3)
               if (x ^ translation) >> j & 1],F)}
        cubes = list(product((None,0,1),repeat=3))
        masks = {}
        for cube in cubes:
            masks[cube] = {x for x in range(8) if all(b is None or x >> i & 1 == b
                             for i,b in enumerate(cube))}
            assert missing_under(cube) == masks[cube] & raw
        known = [c for c in cubes if masks[c] <= raw]
        for terms in [()] + [(c,) for c in known] + list(product(known,repeat=2)):
            union = set().union(*(masks[c] for c in terms))
            relevant = sorted({i for c in terms for i,b in enumerate(c) if b is not None})
            found = set()
            for values in product((0,1),repeat=len(relevant)):
                face = [None]*3
                for i,b in zip(relevant,values):
                    face[i] = b
                if masks[tuple(face)].isdisjoint(union):
                    found |= missing_under(face)
            assert found == raw-union
        point = min(raw)
        singleton = tuple(point >> i & 1 for i in range(3))
        assert len(singleton) > F.q and (point ^ 7) not in raw
        assert any(missing_under(tuple((1-b) if i == j else None
                   for i,b in enumerate(singleton))) for j in range(3))


if __name__ == "__main__":
    for A in ([106,21,90,85,110,81,61], [116,56,41,86,75,71,57]):
        print(A, verify_private(A))
    for n in (8, 10):
        rows = [0]*n
        edges = [(1,2),(0,3)] + [(i,i+1) for i in range(3,n-2)]
        for i,j in edges:
            rows[i] |= 1 << j
            rows[j] |= 1 << i
        result = verify_private(rows)
        assert result == (1,[1 << (n-1)])
        print("path and isolated site", n, result)
    chart_control()
    print("GF2 mandatory chart, two translations, exact known-cube and width-three controls passed")
