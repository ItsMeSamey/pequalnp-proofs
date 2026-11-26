"""Independent exhaustive check of tree objective, original equations and traceback."""
from fractions import Fraction
from random import Random
from semantic_tree_solver import minimize


def check(n,leaves,tree,eq=()):
    def holds(x,rows):
        return all((a&x).bit_count()%2==b for a,b in rows)
    values={x:sum(w for leaf in leaves for w,rows in leaf if holds(x,rows))
            for x in range(1<<n) if holds(x,eq)}
    answer=minimize(n,leaves,tree,eq)
    if not values:
        assert answer is None
    else:
        v,x=answer
        assert v==min(values.values()) and values[x]==v
    return answer


def main():
    # Each pair intersects trivially, but a+b+c=0; pairwise-only joins would claim -3.
    three=[[(-1,[(a,1)])] for a in (1,2,3)]
    assert check(2,three,(0,(1,2)))[0]==-2
    # Global equations create a dependence absent before reparameterization.
    independent=[[(-1,[(1<<i,1)])] for i in range(3)]
    assert check(3,independent,((0,1),2),[(7,0)])[0]==-2
    # A partition of a hyperplane cancels syntactic private variables.
    partition=[(3,[(1,1),(2,0)]),(3,[(1,1),(2,1)]),(-1,[])]
    check(3,[partition,[(Fraction(-5,2),[(1,1),(4,1)])]],(0,1))
    check(0,[],None)
    check(2,[[(1,[])]],0,[(1,0),(1,1)])
    rng=Random(38172)
    for n in range(5):
        for _ in range(12):
            leaves=[[(Fraction(rng.randrange(-4,5),rng.randrange(1,4)),
                      [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))])
                     for _ in range(rng.randrange(5))] for _ in range(4)]
            eq=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
            check(n,leaves,((0,1),(2,3)),eq)
            check(n,leaves,(3,(1,(0,2))),eq)
    print("125 exact objective/witness fixtures, including three-way and Gaussian-induced dependence")


if __name__=='__main__':
    main()
