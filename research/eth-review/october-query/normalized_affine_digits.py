"""Fixed-modulus digits for normalized products of affine forms on a Boolean cube."""
from itertools import combinations, product
from math import prod
from partial_shift_affine import character_sum


def _minor(a, removed):
    keep = [i for i in range(len(a)) if i not in removed]
    return [[a[i][j] for j in keep] for i in keep]


def hafnian(a, k):
    """Hafnian of an integer symmetric zero-diagonal matrix modulo 2**k."""
    if type(k) is not int or k < 1:
        raise ValueError("expected a positive digit width")
    n = len(a)
    if n % 2 or any(len(row) != n for row in a):
        raise ValueError("expected an even square matrix")
    if any(a[i][i] or any(a[i][j] != a[j][i] for j in range(i)) for i in range(n)):
        raise ValueError("expected a symmetric zero-diagonal matrix")
    return _hafnian(a,k)


def _hafnian(matrix,k):
    # Hirai--Namba, Theorem 2.1, scalar specialization. The same-k pivot
    # branch is a loop; recursive branches spend at least one precision bit.
    mod = 1 << k
    a = [[x % mod for x in row] for row in matrix]
    answer, scale = 0, 1
    while a:
        n = len(a)
        if k == 1:
            masks = [sum((v & 1) << j for j,v in enumerate(row)) for row in a]
            invertible = character_sum(n,((row,0) for row in masks),0) == 1
            return (answer + scale*invertible) % mod
        pivot = next((j for j in range(1,n) if a[0][j] & 1),None)
        if pivot is None:
            for j in range(1,n):
                if a[0][j]:
                    answer += scale * a[0][j] * _hafnian(_minor(a,{0,j}),k-1)
            return answer % mod
        if pivot != 1:
            a[1],a[pivot] = a[pivot],a[1]
            for row in a:
                row[1],row[pivot] = row[pivot],row[1]
        for j in range(2,n):
            if not a[0][j] & 1:
                continue
            remaining = [p for p in range(n) if p not in (1,j) and a[1][p]]
            for p,q in combinations(remaining,2):
                x = 2*a[1][p]*a[1][q] % mod
                if x:
                    answer -= scale*x*_hafnian(_minor(a,{1,j,p,q}),k-1)
            for i in range(n):
                if i not in (1,j):
                    a[i][j] = a[j][i] = (a[i][j]+a[i][1]) % mod
        for j in range(2,n):
            if a[0][j]:
                answer += scale * a[0][j] * _hafnian(_minor(a,{0,j}),k-1)
        answer %= mod
        scale = scale*a[0][1] % mod
        a = [row[2:] for row in a[2:]]
    return (answer + scale) % mod

def _injections(rows,columns,k):
    if not rows:
        return 1
    surplus = len(columns)-len(rows)
    if surplus < 0:
        return 0
    nrow = len(rows)
    total = nrow+len(columns)+(surplus & 1)
    a = [[0]*total for _ in range(total)]
    for i,row in enumerate(rows):
        for j,col in enumerate(columns):
            a[i][nrow+j] = a[nrow+j][i] = row[col+1]
    for i in range(nrow,total):
        for j in range(nrow,i):
            a[i][j] = a[j][i] = 1
    extensions = prod(range(1,surplus+(surplus & 1),2))
    mod = 1 << k
    return _hafnian(a,k)*pow(extensions,-1,mod) % mod


def _collision_terms(rows,f,k):
    """Enumerate exceptional rows exactly once, then price injective completions."""
    r = len(rows)
    mod = 1 << k
    answer = 0
    for size in range(min(r,2*(k-1))+1):
        for chosen in combinations(range(r),size):
            residual = [row for i,row in enumerate(rows) if i not in chosen]
            options = [[j for j in range(f+1) if rows[i][j] % mod] for i in chosen]
            for assignment in product(*options):
                used = {j for j in assignment if j}
                # Positive options are outside-coordinate indices plus one.
                if any(assignment.count(j)<2 for j in used):
                    continue
                excess = size-len(used)
                if excess >= k:
                    continue
                coefficient = 1 << excess
                for i,j in zip(chosen,assignment):
                    coefficient = coefficient*rows[i][j] % mod
                if coefficient:
                    columns = [j for j in range(f) if j+1 not in used]
                    answer += coefficient*_injections(residual,columns,k)
                    answer %= mod
    return answer

def _parity_defect(row,k):
    """Sparse monomials of H minus its zero-one affine binary parity modulo 2**k."""
    mod = 1 << k
    c = row[0] & 1
    support = [j for j,a in enumerate(row[1:]) if a & 1]
    terms = []
    if (row[0]-c) % mod:
        terms.append((0,(row[0]-c) % mod))
    for j,a in enumerate(row[1:]):
        diff = (a - (1-2*c)*(a & 1)) % mod
        if diff:
            terms.append((1 << j,diff))
    for deg in range(2,min(k,len(support))+1):
        coeff = -(1-2*c)*(-2)**(deg-1) % mod
        for subset in combinations(support,deg):
            terms.append((sum(1 << j for j in subset),coeff))
    return terms


def _parity_terms(rows,f,k):
    mod = 1 << k
    equations = [(sum((v & 1) << j for j,v in enumerate(row[1:])),1 ^ (row[0] & 1))
                 for row in rows]
    defects = [_parity_defect(row,k) for row in rows]
    indices = [i for i,terms in enumerate(defects) if terms]
    answer = 0
    for size in range(min(k-1,len(indices))+1):
        for selected in combinations(indices,size):
            fixed = [eq for i,eq in enumerate(equations) if i not in selected]
            for monomials in product(*(defects[i] for i in selected)):
                pins,coefficient = 0,1
                for mask,value in monomials:
                    pins |= mask
                    coefficient = coefficient*value % mod
                if coefficient:
                    eq = fixed+[(1 << j,1) for j in range(f) if pins >> j & 1]
                    answer += coefficient*character_sum(f,eq,0)
                    answer %= mod
    return answer


def normalized_product(rows,f,k):
    """Return 2**(r-max(r,f)) times sum_x product_i H_i(x) modulo 2**k.

    A row encodes its affine constant followed by f integer coefficients.
    Only their residues mod 2**k are needed. No division in the residue ring.
    """
    if type(f) is not int or f < 0 or type(k) is not int or k < 1:
        raise ValueError("invalid dimension or digit width")
    rows = [tuple(row) for row in rows]
    if any(len(row) != f+1 or any(type(v) is not int for v in row) for row in rows):
        raise ValueError("every row needs an integer constant and f coefficients")
    if len(rows) <= f:
        return _collision_terms(rows,f,k)
    return _parity_terms(rows,f,k)
