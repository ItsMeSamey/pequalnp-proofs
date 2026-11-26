"""Check full (V,z)-jet rank bound for the unpinned flat-guard construction."""
from functools import cache
from itertools import product
from sympy import Matrix
from tanner_lift_check import digits

K, J, ELL = 4, 2, 3
INDEX = list(product(range(ELL),range(J+1)))
ONE = {(0,0):1}


def multiply(a,b):
    result = {}
    for (v,z),x in a.items():
        for (w,j),y in b.items():
            if v+w<ELL and z+j<=J:
                k = v+w,z+j
                result[k] = result.get(k,0)+x*y
    return result


@cache
def lift(c,t):
    from sympy import Poly, symbols
    y = symbols('y')
    arg = Poly(c+t*y,y)
    h = arg*(arg-1)
    data = {}
    for v,e in enumerate(digits(ELL)):
        value = (arg*int(e.nth(1))+int(e.nth(0)))*h**v
        for j in range(J+1):
            if value.nth(j):
                data[v,j] = int(value.nth(j))
    return data


@cache
def first(a,x):
    value = ONE
    for i in range(K):
        value = multiply(value,lift(((a>>i)&1)+((x>>i)&1),0))
    return value


@cache
def second(s,u):
    value = ONE
    for i in range(K):
        value = multiply(value,lift((s>>i)&1,-((u>>i)&1)))
    return value


if __name__=='__main__':
    selectors = [s for s in range(2**K) if s.bit_count()==J]
    truth = []
    queries = [[] for _ in range(3)]
    for a in selectors:
        row = []
        query_rows = [[] for _ in queries]
        for s in selectors:
            diag = sum(multiply(first(a,x),second(s,x)).get((0,J),0) for x in range(2**K))
            row.append(diag)
            for seed, current in enumerate(query_rows):
                ans = 0
                for x in range(2**K):
                    # Two anchor slices; unused guards give a common multiplicity.
                    for anchor in (0,1):
                        w = ((31*x+seed+7*anchor)**2 % 29)-12
                        jet = multiply(first(a,x),second(s,(5+seed)%16)) if anchor else ONE
                        ans += w*sum((2+z+seed*v+3*v*z)*c for (v,z),c in jet.items())
                current.append(ans)
        truth.append(row)
        for query, vals in zip(queries,query_rows):
            query.append(vals)
    assert Matrix(truth)==(-1)**J*Matrix.eye(len(selectors))
    ranks = [Matrix(q).rank() for q in queries]
    assert max(ranks)<=ELL+1
    print('diagonal rank',len(selectors),'whole-jet query ranks',ranks)
