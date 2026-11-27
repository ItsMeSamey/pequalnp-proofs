import networkx
from fractions import Fraction
from itertools import product
from random import Random
from read_two_min_cost import minimum_cost


def check(costs,clauses,pins):
    def valid(x):
        return all(x[i]==v for i,v in pins.items()) and all(
            any(x[i] in allowed for i,allowed in c) for c in clauses)
    feasible=[(sum(costs[i][v] for i,v in enumerate(x)),x)
              for x in product(*costs) if valid(x)]
    got=minimum_cost(costs,clauses,pins=pins)
    if not feasible:
        assert got is None
    else:
        assert got in feasible and got[0]==min(value for value,x in feasible)


def main():
    rng=Random(32323)
    for _ in range(150):
        n=rng.randrange(6)
        costs=[{v:Fraction(rng.randrange(-8,9),rng.randrange(1,5)) for v in 'abc'} for i in range(n)]
        clauses=[[] for _ in range(rng.randrange(5))]
        for i in range(n):
            for j in range(rng.randrange(3) if clauses else 0):
                rng.choice(clauses).append((i,tuple(v for v in 'abcd' if rng.randrange(2))))
        pins={i:rng.choice('abcd') for i in range(n) if rng.randrange(5)==0}
        check(costs,clauses,pins)
    check([{}],[],{})
    # Each variable can select neither, either, or both clause endpoints.
    # Sweep all endpoint costs across cheap and expensive joint coverage.
    clauses=[[(0,('L','B')),(1,('L','B'))],[(0,('R','B')),(1,('R','B'))]]
    for joint0,joint1 in product((-2,0,4),repeat=2):
        prices=[{'N':-1,'L':Fraction(1,2),'R':Fraction(2,3),'B':b}
                for b in (joint0,joint1)]
        for a,b in product((None,'N','L','R','B'),repeat=2):
            pins={i:v for i,v in enumerate((a,b)) if v is not None}
            check(prices,clauses,pins)
    for a,b in product(('L','R','B'),repeat=2):
        check([{'L':-1,'R':0,'B':1}], [[(0,(a,)),(0,(a,)),(0,(b,)),(0,())],
              [(0,('B',))]], {})
    try:
        minimum_cost([{1:0}], [[(0,(1,))]]*3)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted a variable in three distinct clauses")
    print('385 direct cost/witness tests and distinct-clause rejection passed; NetworkX',
          networkx.__version__)


if __name__=='__main__':
    main()
