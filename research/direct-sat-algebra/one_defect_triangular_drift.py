"""Minimum lower-prefix completion and marked-support decision by affine DAG transitions."""
from itertools import combinations
from quadratic_target import insert,reduce_vector,parity,apply_basis


def minimum_completion(rows):
    """Complete prescribed row i bits strictly below i, minimizing binary rank."""
    n=len(rows)
    generators=[]
    completed=[0]*n
    for i in reversed(range(n)):
        mask=(1<<i)-1
        prefix={}
        for j,v in enumerate(generators):
            insert(v&mask,1<<j,prefix)
        rem,c=reduce_vector(rows[i]&mask,prefix)
        if rem:
            v=rows[i]&mask
            generators.append(v)
        else:
            v=apply_basis(generators,c)
        completed[i]=v
    basis={}
    for j,v in enumerate(generators):
        insert(v,1<<j,basis)
    return generators,[reduce_vector(v,basis)[1] for v in completed]


def search(rows,beta,*,rank_cap=None):
    n=len(rows)
    if any(v<0 or v>=1<<n for v in (*rows,beta)) or (rank_cap is not None and rank_cap<0):
        raise ValueError("invalid matrix, mark, or cap")
    if not beta:
        return 'NO',None,{}
    V,U=minimum_completion(rows)
    r=len(V)
    if rank_cap is not None and r>rank_cap:
        return 'UNKNOWN',None,dict(rank=r)
    D=[a^apply_basis(V,b) for a,b in zip(rows,U)]
    terms=[sum(1<<i for i in S) for size in range(min(n,r+1)+1) for S in combinations(range(n),size)]
    def features(z):
        return sum((z&m==m)<<i for i,m in enumerate(terms))
    for signal in range(1<<r):
        reps=[0]
        for i in reversed(range(n)):
            echelon={}
            new=[]
            for z in reps:
                candidates=[z]
                if not (parity(D[i]&z)^((D[i]>>i)&1)^parity(U[i]&signal)):
                    candidates.append(z|(1<<i))
                for x in candidates:
                    if insert(features(x),0,echelon):
                        new.append(x)
            reps=new
        for z in reps:
            if parity(z&beta) and all(parity(v&z)==(signal>>j&1) for j,v in enumerate(V)):
                assert all(not(z>>i&1 and parity(v&z)) for i,v in enumerate(rows))
                return 'YES',z,dict(rank=r,features=len(terms))
    return 'NO',None,dict(rank=r,features=len(terms))
