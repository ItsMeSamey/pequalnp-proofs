"""Exact ranks for binary and ternary sign-clause matching constructions."""
from fractions import Fraction


def rank(matrix, p):
    basis = {}
    norm = (lambda x: x % p) if p else Fraction
    for src in matrix:
        row = list(map(norm, src))
        for pivot in sorted(basis):
            if row[pivot]:
                c = row[pivot]
                row = [norm(a-c*b) for a,b in zip(row,basis[pivot])]
        pivot = next((i for i,x in enumerate(row) if x),None)
        if pivot is not None:
            inverse = pow(row[pivot],-1,p) if p else 1/row[pivot]
            basis[pivot] = [norm(x*inverse) for x in row]
    return len(basis)


def monomial_coeff(sign, subset, block):
    # coefficient in one minus the indicator polynomial for the forbidden sign
    pos = sign & block
    if pos & ~subset:
        return int(not subset)
    return int(not subset) - (-1)**((subset ^ pos).bit_count())


def verify(matchings, n, p):
    m = 1 << n
    points = range(m)
    assert len(set(matchings[0]+matchings[1]))==len(matchings[0]+matchings[1])
    for matching in matchings:
        assert sum(matching) == m-1 and sum(b.bit_count() for b in matching)==n
    x_eval = [[int(all((a^sign)&b for b in matchings[0])) for a in points] for sign in points]
    # Enumerate coefficient basis before substituting Y_i=−zX_i.
    y_coeff = []
    for sign in points:
        row = []
        for subset in points:
            coeff = 1
            for block in matchings[1]:
                coeff *= monomial_coeff(sign,subset & block,block)
            row.append(coeff)
        y_coeff.append(row)
    ranks = (rank(x_eval,p),rank(y_coeff,p))
    if ranks==(m,m):
        for q in range(n+2):
            subsets = [s for s in points if s.bit_count()<=q]
            diagonal = [[int(a&s==s) for s in subsets] for a in points]
            assert rank(diagonal,p)==len(subsets)
    return ranks


if __name__=='__main__':
    families = [(4,((3,12),(5,10))), (6,((7,56),(11,52)))]
    for n,matchings in families:
        for p in (0,2,3,7):
            result = verify(matchings,n,p)
            local = 1 << (n//2)
            expected = (local - int(bool(p) and (local-1)%p==0))**2
            assert result == (expected,expected)
            print(n,p,result)
