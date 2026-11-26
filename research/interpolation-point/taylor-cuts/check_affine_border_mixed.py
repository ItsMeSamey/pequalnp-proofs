"""Independent checks of mixed Boolean equations and signed direct 3-CNF."""
from itertools import combinations
from random import Random
from affine_border_mixed import FaceBudgetExceeded, solve_anf, solve_cnf3, _rules, _faces, _tables


def compare(result,models):
    count,witness=result
    assert count==len(models) and (witness in models if models else witness is None)


def check(n,rows):
    models=[x for x in range(1<<n)
            if all(sum(all(x>>j&1 for j in range(n) if m>>j&1) for m in row)%2==0 for row in rows)]
    compare(solve_anf(n,rows,max_faces=128),models)
    if models:
        reduced=[{m for m in row if row.count(m)%2} for row in rows]
        rules=_rules(reduced)
        faces=_faces(n,rules,128)
        matrices=_tables(n,rules,faces)
        for x in models:
            vec=sum((c&x==c)<<j for j,c in enumerate(faces))
            for i,matrix in enumerate(matrices):
                assert sum(((r&vec).bit_count()%2)<<j for j,r in enumerate(matrix))==(vec if x>>i&1 else 0)


if __name__=='__main__':
    rng=Random(769)
    for _ in range(400):
        n=rng.randrange(7)
        rows=[rng.choices(range(1<<n),k=rng.randrange(9)) for _ in range(rng.randrange(9))]
        check(n,rows)
    for _ in range(350):
        n=rng.randrange(1,8)
        clauses=[[rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))]
                 for _ in range(rng.randrange(22))]
        models=[x for x in range(1<<n)
                if all(any(bool(x>>(abs(lit)-1)&1)==(lit>0) for lit in clause) for clause in clauses)]
        compare(solve_cnf3(n,clauses,max_faces=128),models)
    for n in (3,5,7):
        cubics=[[-(i+1),-(j+1),-(k+1)] for i,j,k in combinations(range(n),3)]
        count,wit=solve_cnf3(n,cubics,max_faces=1+n+n*(n-1)//2)
        assert count==1+n+n*(n-1)//2 and wit is not None
    check(5,[[3,5,8,0],[3,5,8]])  # Gaussian constant contradiction
    check(5,[[14,3,5],[25,14,7,3],[11,10,1],[5,2,0],[1,0]])
    assert solve_cnf3(0,[[]])==(0,None) and solve_cnf3(0,[])==(1,0)
    try:solve_anf(12,[],max_faces=100)
    except FaceBudgetExceeded:pass
    else:raise AssertionError('face budget missing')
    print('400 arbitrary-degree ANFs, 350 direct signed 3-CNFs, dense cubic controls and edge cases passed')
