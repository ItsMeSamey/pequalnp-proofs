"""Charge-limited clause ANFs, affine consequences, and a CNF witness wrapper."""
from affine_boundary_conflict import _violation,_boundary_rows
from semantic_tree_solver import minimize


def _prepare(n,clauses):
    if type(n) is not int or n<0:
        raise ValueError("invalid variable count")
    rows=[tuple(dict.fromkeys(c)) for c in clauses]
    if any(type(lit) is not int or not 1<=abs(lit)<=n for c in rows for lit in c):
        raise ValueError("invalid literal")
    return rows


def consequences(n,clauses,*,budget=4096):
    """Return (contradiction source bitmask or None, certified affine equations).

    Each equation is (normal, rhs, original-clause index bitmask). Budget
    limits the total number of initial ANF monomials materialized.
    """
    rows=_prepare(n,clauses)
    if type(budget) is not int or budget<0:
        raise ValueError("invalid ANF budget")
    choices=[]
    for i,c in enumerate(rows):
        signs=set(c)
        if any(-lit in signs for lit in c):
            continue
        power=sum(lit>0 for lit in c)
        if power<budget.bit_length():
            choices.append((power,i))
    selected=[]
    for power,i in sorted(choices):
        cost=1<<power
        if cost>budget:
            break
        selected.append(i)
        budget-=cost
    basis={}
    for polynomial,mask in _boundary_rows((_violation(rows[i]) for i in selected),(1<<n)-1):
        normal=sum(m for m in polynomial if m)
        rhs=int(0 in polynomial)
        source=0
        while mask:
            bit=mask&-mask
            source|=1<<selected[bit.bit_length()-1]
            mask-=bit
        while normal:
            j=normal.bit_length()-1
            if j not in basis:
                basis[j]=(normal,rhs,source)
                break
            v,b,src=basis[j]
            normal^=v
            rhs^=b
            source^=src
        else:
            if rhs:
                return source,tuple(basis.values())
    return None,tuple(basis.values())


def replay(n,clauses,normal,rhs,source,*,budget=4096):
    rows=_prepare(n,clauses)
    if type(source) is not int or source<0 or source.bit_length()>len(rows):
        return False
    if type(normal) is not int or normal<0 or normal.bit_length()>n or rhs not in (0,1):
        return False
    polynomial=set()
    for i,c in enumerate(rows):
        if source>>i&1:
            literals=set(c)
            if any(-x in literals for x in literals):
                continue
            power=sum(x>0 for x in literals)
            if power>=budget.bit_length() or (1<<power)>budget:
                return False
            budget-=1<<power
            polynomial^=_violation(c)
    expected={1<<i for i in range(n) if normal>>i&1}
    if rhs:
        expected.add(0)
    return polynomial==expected


def solve_cnf(n,clauses,*,budget=4096,tree=None):
    """Return an original satisfying assignment mask or None, not a MaxSAT optimum."""
    rows=_prepare(n,clauses)
    conflict,affine=consequences(n,rows,budget=budget)
    if conflict is not None:
        return None
    leaves=[[(1,[(1<<(abs(x)-1),int(x<0)) for x in c])] for c in rows]
    if tree is None and leaves:
        nodes=list(range(len(leaves)))
        while len(nodes)>1:
            nodes=[(nodes[j],nodes[j+1]) if j+1<len(nodes) else nodes[j] for j in range(0,len(nodes),2)]
        tree=nodes[0]
    result=minimize(n,leaves,tree,[(a,b) for a,b,_ in affine])
    if result is None or result[0]!=0:
        return None
    witness=result[1]
    if not all(any(bool(witness & (1<<(abs(x)-1)))==(x>0) for x in c) for c in rows):
        raise AssertionError("failed original-coordinate witness replay")
    return witness
