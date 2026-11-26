from itertools import product
from random import Random
from complete_solver import search, bits
from check_noncomplete import brute


def check(rows, left, right):
    got = search(rows,left,right)
    assert (got is not None) == brute(rows,left,right), (rows,left,right,got)
    if got is not None:
        x=got & ((1<<len(left))-1)
        y=got>>len(left)
        assert sum(left[i]!=2 for i in bits(x))%2 == sum(right[j]!=2 for j in bits(y))%2 == 1
        assert (sum(left[i]!=0 for i in bits(x))+sum(right[j]!=0 for j in bits(y)))%2 == 0
        assert all((rows[i]&y).bit_count()%2==0 for i in bits(x))
        assert all(sum(rows[i]>>j&1 for i in bits(x))%2==0 for j in bits(y))


if __name__ == '__main__':
    tested = 0
    # Three vertices per side, all profiles with one or two shared vertices.
    for p,q in product((1,2), repeat=2):
        for colors in product(range(2), repeat=p+q):
            left = colors[:p]+(2,)*(3-p)
            right = colors[p:]+(2,)*(3-q)
            free = [(i,j) for i in range(3) for j in range(3) if i>=p or j>=q]
            for raw in range(1<<len(free)):
                rows = [(1<<q)-1 if i<p else 0 for i in range(3)]
                for k,(i,j) in enumerate(free):
                    rows[i] |= ((raw >> k)&1) <<j
                check(rows,left,right)
                tested+=1
    rng = Random(9105)
    for _ in range(3000):
        left=[rng.randrange(3) for _ in range(rng.randrange(1,8))]
        right=[rng.randrange(3) for _ in range(rng.randrange(1,8))]
        rows=[sum((1 if r!=2 and s!=2 else rng.randrange(2))<<j for j,s in enumerate(right)) for r in left]
        check(rows,left,right)
        tested+=1
    # Isolate matching is necessary: a colored square with two extra colored
    # right vertices and two left shared isolates providing the correction.
    check([15,9,3,5], [0,2,2,2], [1,0,1,2])
    assert search([15,9,3,5], [0,2,2,2], [1,0,1,2]) == 255
    print("Checked",tested,"exhaustive/seeded instances and the eight-vertex example.")
