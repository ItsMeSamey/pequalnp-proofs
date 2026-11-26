"""Exact counting for explicit Boolean ANFs of mixed degree, including cubic CNF."""
from affine_border_solver import _bits, _candidates


class FaceBudgetExceeded(ValueError):
    """More standard faces than the caller's iteration budget."""


def _rules(rows):
    monomials = sorted(set().union(*rows) if rows else (),key=lambda m:(m.bit_count(),m))
    index = {m:i for i,m in enumerate(monomials)}
    pivots = {}
    for terms in rows:
        eq = sum(1<<index[m] for m in terms)
        while eq:
            j = eq.bit_length()-1
            if j not in pivots:
                pivots[j] = eq
                break
            eq ^= pivots[j]
    pivot_mask = sum(1<<j for j in pivots)
    rules = {}
    for j in sorted(pivots):
        rest = pivots[j] ^ (1<<j)
        for b in _bits(rest & pivot_mask):
            rest ^= pivots[b.bit_length()-1]
        pivots[j] = rest | (1<<j)
        rules[monomials[j]] = tuple(monomials[b.bit_length()-1] for b in _bits(rest))
    return rules


def _faces(n, rules, budget):
    faces = []
    stack = [(0,0)]
    while stack:
        c,start = stack.pop()
        faces.append(c)
        if budget is not None and len(faces)>budget:
            raise FaceBudgetExceeded("standard-face count exceeds max_faces")
        for j in range(start,n):
            new = c | (1<<j)
            if not any(new & p == p for p in rules):
                stack.append((new,j+1))
    return faces


def _tables(n, rules, faces):
    normal = {c:1<<j for j,c in enumerate(faces)}
    border = {c | (1<<i) for c in faces for i in range(n)} - normal.keys()
    for z in sorted(border,key=lambda m:(m.bit_count(),m)):
        pivot = next(m for m in rules if m & z == m)
        q = z ^ pivot
        value = 0
        for term in rules[pivot]:
            expansion = normal[q]
            for bit in _bits(term):
                updated = 0
                for idx in _bits(expansion):
                    c = faces[idx.bit_length()-1]
                    updated ^= normal[c | bit]
                expansion = updated
            value ^= expansion
        normal[z] = value
    return [[normal[c | (1<<i)] for c in faces] for i in range(n)]


def solve_anf(n, rows, *, max_faces=None):
    """Return (count, witness or None) for XOR-of-monomials rows equated to zero.

    A monomial is its n-bit variable mask and 0 is the constant one. Repeating
    a monomial in a row cancels it. max_faces includes the empty face.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    if max_faces is not None and (not isinstance(max_faces,int) or max_faces<0):
        raise ValueError("invalid face budget")
    equations = []
    for row in rows:
        terms = set()
        for m in row:
            if not isinstance(m,int) or m<0 or m.bit_length()>n:
                raise ValueError("invalid monomial mask")
            if m in terms:
                terms.remove(m)
            else:
                terms.add(m)
        equations.append(terms)
    rules = _rules(equations)
    if 0 in rules:
        return 0,None
    faces = _faces(n,rules,max_faces)
    tables = _tables(n,rules,faces)
    count,witness = 0,None
    for x in _candidates(faces,tables):
        if all(sum((x&m)==m for m in row)%2==0 for row in equations):
            count += 1
            if witness is None:
                witness = x
    return count,witness


def _cnf_rows(n, clauses, width_limit):
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    rows = []
    for clause in clauses:
        literals = set(clause)
        if any(not isinstance(lit,int) or not 1<=abs(lit)<=n for lit in literals):
            raise ValueError("invalid literal")
        if any(-lit in literals for lit in literals):
            continue
        if width_limit is not None and len(literals)>width_limit:
            raise ValueError("clause width exceeds three")
        # Falsity is product of x_i for negative and 1+x_i for positive literals.
        negative = sum(1<<(-lit-1) for lit in literals if lit<0)
        terms = [negative]
        for lit in literals:
            if lit>0:
                bit = 1<<(lit-1)
                terms += [m | bit for m in terms]
        rows.append(terms)
    return rows


def solve_cnf(n, clauses, *, max_faces=None):
    """Arbitrary signed DIMACS CNF; each non-tautological clause adds 2^p terms,
    where p counts distinct positive literals. Total expansion ≤ sum_C 2^width(C).
    """
    return solve_anf(n,_cnf_rows(n,clauses,None),max_faces=max_faces)


def solve_cnf3(n, clauses, *, max_faces=None):
    """Count signed CNFs of width at most three; DIMACS literals are ±1,...,±n."""
    return solve_anf(n,_cnf_rows(n,clauses,3),max_faces=max_faces)
