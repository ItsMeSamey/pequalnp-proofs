"""Boolean quadratic equations in algebraic normal form, evaluated over GF(2)."""
from affine_border_solver import CliqueBudgetExceeded, _candidates, _monomials, _rules, _tables


def solve_quadratic_anf(n, rows, *, max_cliques=None):
    """Return (exact model count, one witness or None).

    Each row is an iterable of squarefree monomial masks whose XOR must be zero.
    A zero mask denotes 1, a one-bit mask denotes a variable, and a two-bit
    mask denotes its two variables' product. Repetition cancels. Example:
    [[0, 1, 3, 12]] imposes 1 + x0 + x0*x1 + x2*x3 = 0 on four bits.
    The optional budget counts all cliques, including the empty clique.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("dimension must be a nonnegative integer")
    if max_cliques is not None and (not isinstance(max_cliques,int) or max_cliques<0):
        raise ValueError("max_cliques must be a nonnegative integer")
    monomials = _monomials(n)
    positions = {m:i for i,m in enumerate(monomials)}
    original = []
    encoded = []
    for row in rows:
        terms = set()
        bits = 0
        for m in row:
            if not isinstance(m,int) or m not in positions:
                raise ValueError("monomial mask outside the degree-two variable universe")
            if m in terms:
                terms.remove(m)
            else:
                terms.add(m)
            bits ^= 1 << positions[m]
        original.append(tuple(terms))
        encoded.append(bits)
    if 1 in encoded:
        return 0,None
    rules = _rules(n,monomials,encoded)
    cliques,tables = _tables(n,rules,max_cliques)
    count = 0
    witness = None
    for x in _candidates(cliques,tables):
        if all(sum((x & term)==term for term in row)%2==0 for row in original):
            count += 1
            if witness is None:
                witness = x
    return count,witness
