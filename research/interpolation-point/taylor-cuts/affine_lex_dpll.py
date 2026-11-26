"""Pure-lex Gaussian branching for explicitly expanded Boolean ANFs."""
from affine_border_mixed import _cnf_rows


def _input_rows(n, rows):
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid variable count")
    result=[]
    for row in rows:
        terms=set()
        for m in row:
            if not isinstance(m,int) or m<0 or m.bit_length()>n:
                raise ValueError("invalid monomial mask")
            terms.symmetric_difference_update((m,))
        if terms:
            result.append(frozenset(terms))
    return tuple(result)


def _echelon(rows):
    """Ordered leading masks are numerical (pure lex), including constant mask 0."""
    pivots={}
    for row in rows:
        row=frozenset(row)
        while row:
            pivot=max(row)
            if pivot not in pivots:
                if pivot==0:
                    return (frozenset((0,)),)
                pivots[pivot]=row
                break
            row=row ^ pivots[pivot]
    return tuple(pivots.values())


def _restrict(rows, bit, value):
    out=[]
    for row in rows:
        if value:
            fixed=set()
            for m in row:
                fixed.symmetric_difference_update((m & ~bit,))
        else:
            fixed={m for m in row if not m & bit}
        if fixed:
            out.append(frozenset(fixed))
    return tuple(out)


def solve_lex_anf(n, rows):
    """Return (exact count, witness or None); each row is an XOR of masks equated to zero."""
    rows=_input_rows(n,rows)
    stack=[(rows,(1<<n)-1,0)]
    total=0
    witness=None
    while stack:
        pending,free,prefix=stack.pop()
        eqs=_echelon(pending)
        if eqs==(frozenset((0,)),):
            continue
        if not eqs:
            total += 1 << free.bit_count()
            if witness is None:
                witness=prefix
            continue
        live=0
        for row in eqs:
            for monomial in row:
                live |= monomial
        bit=live & -live
        rest=free ^ bit
        for v in (1,0):
            stack.append((_restrict(pending,bit,v),rest,prefix | (bit if v else 0)))
    return total,witness


def solve_lex_cnf(n, clauses):
    """Arbitrary signed DIMACS CNF; pre-expand 2^p terms per non-tautological clause
    with p distinct positive literals. The runtime bound uses the expanded size.
    """
    return solve_lex_anf(n,_cnf_rows(n,clauses,None))


def solve_factored_cnf(n, clauses):
    """Unexpanded signed DIMACS DPLL. The face bound uses original clause scopes."""
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid variable count")
    parsed=set()
    for clause in clauses:
        pos=neg=0
        for lit in clause:
            if not isinstance(lit,int) or not 1<=abs(lit)<=n:
                raise ValueError("invalid literal")
            bit=1<<(abs(lit)-1)
            if lit>0:
                pos |= bit
            else:
                neg |= bit
        if not pos & neg:
            parsed.add((pos,neg))
    stack=[(parsed,(1<<n)-1,0)]
    total=0
    witness=None
    while stack:
        active,free,prefix=stack.pop()
        if (0,0) in active:
            continue
        if not active:
            total += 1<<free.bit_count()
            if witness is None:
                witness=prefix
            continue
        live=0
        for pos,neg in active:
            live |= pos | neg
        bit=live&-live
        for v in (1,0):
            child={(pos & ~bit,neg & ~bit) for pos,neg in active if not ((pos if v else neg)&bit)}
            stack.append((child,free^bit,prefix | (bit if v else 0)))
    return total,witness
