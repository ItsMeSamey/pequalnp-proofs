"""Check every edge of small Gaussian search trees against independent face enumeration."""
from random import Random
from itertools import permutations
from affine_lex_dpll import solve_lex_anf, solve_lex_cnf, solve_factored_cnf, _input_rows, _echelon, _restrict


def submasks(mask):
    v=mask
    while True:
        yield v
        if not v:
            return
        v=(v-1)&mask


def faces(rows,free):
    pivots=[max(row) for row in rows]
    return {t for t in submasks(free) if not any(t&p==p for p in pivots)}


def verify(n, raw):
    rows=_input_rows(n,raw)
    root=(1<<n)-1
    def accepted(x):
        return all(sum(int(x&m==m) for m in row)%2==0 for row in raw)
    models=[x for x in range(1<<n) if accepted(x)]
    count,witness=solve_lex_anf(n,raw)
    assert count==len(models) and (witness in models if models else witness is None)
    checks=0
    root_mass=len(faces(_echelon(rows),root))
    per_level={}
    terminal_mass=0
    stack=[(_echelon(rows),root)]
    while stack:
        eqs,free=stack.pop()
        F=faces(eqs,free)
        level=n-free.bit_count()
        per_level[level]=per_level.get(level,0)+len(F)
        if not F or not eqs:
            terminal_mass+=len(F)
            continue
        live=0
        for row in eqs:
            for m in row:
                live |= m
        i=live&-live
        children=[_echelon(_restrict(eqs,i,v)) for v in (0,1)]
        left,right=(faces(child,free^i) for child in children)
        assert len(left)+len(right)<=len(F)
        for t in submasks(free^i):
            assert int(t in left)+int(t in right)<=int(t in F)+int((t|i) in F)
        stack.extend((child,free^i) for child in children)
        checks+=1
    assert all(mass<=root_mass for mass in per_level.values()) and terminal_mass<=root_mass
    return checks


if __name__=='__main__':
    rng=Random(801)
    checks=0
    for _ in range(450):
        n=rng.randrange(8)
        raw=[rng.choices(range(1<<n),k=rng.randrange(9)) for _ in range(rng.randrange(8))]
        checks+=verify(n,raw)
    for raw in ([],[[]],[[0]],[[0,0]],[[6,7],[2,3,4],[1,0]],[[3],[3,0]],
                [[1,2],[2,3]],[[6,7,8,3],[4,5,12],[9,8,1,0]]):
        checks+=verify(4,raw)
    for _ in range(150):
        n=rng.randrange(1,8)
        clauses=[[rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(7))]
                 for j in range(rng.randrange(8))]
        models=[x for x in range(1<<n) if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)]
        for solver in (solve_lex_cnf,solve_factored_cnf):
            count,w=solver(n,clauses)
            assert count==len(models) and (w in models if models else w is None)
    systems=0
    for n,expected in ((0,2),(1,5),(2,67)):
        cols=1<<n
        spaces={frozenset({0})}
        todo=list(spaces)
        while todo:
            space=todo.pop()
            for v in range(1,1<<cols):
                if v not in space:
                    big=space | {v^w for w in space}
                    if big not in spaces:
                        spaces.add(big);todo.append(big)
        assert len(spaces)==expected
        for space in spaces:
            for perm in permutations(range(n)):
                pm=[sum(((m>>j)&1)<<perm[j] for j in range(n)) for m in range(cols)]
                rows=[[pm[m] for m in range(cols) if vec>>m&1] for vec in space]
                checks+=verify(n,rows);systems+=1
    for n in (3,4):
        for trial in range(8):
            rows=[rng.choices(range(1<<n),k=rng.randrange(1,8)) for _ in range(4)]
            for perm in permutations(range(n)):
                pm=[sum(((m>>j)&1)<<perm[j] for j in range(n)) for m in range(1<<n)]
                checks+=verify(n,[[pm[m] for m in row] for row in rows]);systems+=1
    assert solve_factored_cnf(100,[range(1,101)])[0]==(1<<100)-1
    assert solve_lex_anf(1200,[[1<<1199]])==(1<<1199,0)
    print(f'450 ANFs, 150 native signed CNFs, fixtures and sparse large dimension passed; {systems} exhaustive/sampled all-order systems, {checks} entire-branch pointwise face inequalities verified')
