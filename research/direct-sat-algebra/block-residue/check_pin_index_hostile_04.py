"""04-only direct Boolean model oracle for SCC unit compatibility."""
from itertools import combinations, product
from indexed_ordered_row_csp import PinIndex


def check(n, rows):
    def accepts(x, l):
        return bool(x >> (abs(l)-1) & 1) == (l>0)
    models = [x for x in range(1<<n) if all(any(accepts(x,l) for l in row) for row in rows)]
    index = PinIndex(n,rows)
    assert index.consistent == bool(models)
    lits = [s*i for i in range(1,n+1) for s in (-1,1)]
    for size in range(len(lits)+1):
        for pins in combinations(lits,size):
            expected = any(all(accepts(x,l) for l in pins) for x in models)
            assert index.compatible(iter(pins+pins)) == expected


def main():
    check(0,[])
    check(0,[()])
    formulas = [[], [()], [(1,),(-1,)], [(-1,2),(-2,3),(-3,-1)],
                [(-1,2),(-2,1),(-3,4),(-4,3),(-2,-4)],
                [(-1,2),(-1,3),(-2,-4),(-3,4)],
                [(1,-1),(2,2),(-2,3),(-3,4),(-4,4)]]
    for rows in formulas:
        check(4,rows)
    universe = [(1,2),(1,-2),(-1,2),(-1,-2),(1,),(-2,)]
    for mask in range(1<<len(universe)):
        check(2,[r for i,r in enumerate(universe) if mask>>i&1])
    # Independent exhaustive chain oracle without recursive SCC traversals.
    n = 1200
    chain = PinIndex(n, [(-i,i+1) for i in range(1,n)])
    assert chain.compatible([1,n]) and not chain.compatible([1,-n])
    assert chain.compatible([-1,n]) and not chain.compatible([n,-n])
    for bad in (0, n+1, -n-1):
        try:
            chain.compatible([bad])
        except ValueError:
            pass
        else:
            raise AssertionError("invalid unit accepted")
    print("hostile SCC-DAG unit compatibility passed")


if __name__ == "__main__":
    main()
