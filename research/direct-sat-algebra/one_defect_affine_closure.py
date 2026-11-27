"""Alternating certified affine restriction and binary-clause closure."""
from itertools import combinations
from one_defect_clause_closure import samples
from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def search(rows,beta,pivot=None):
    n=len(rows)
    if any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid matrix or mark")
    if not beta:
        return 'NO',None,[]
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("pivot must be marked")
    origin=1<<pivot
    dirs=[(1<<i)^(((beta>>i)&1)<<pivot) for i in range(n) if i!=pivot]
    H=set()
    trace=[]
    while True:
        N=len(dirs)
        trace.append((N,len(H)))
        pts=samples(N,H)
        if not pts:
            return 'NO',None,trace
        values=[0]*n
        for j,y in enumerate(pts):
            z=origin^apply_basis(dirs,y)
            fail=[i for i,r in enumerate(rows) if z>>i&1 and parity(r&z)]
            if not fail:
                return 'YES',z,trace
            for i in fail:
                values[i]|=1<<j
        space={}
        for v in values:
            insert(v,0,space)
        ones=(1<<len(pts))-1
        axes=[sum(((y>>i)&1)<<j for j,y in enumerate(pts)) for i in range(N)]
        affine={}
        equations=[]
        for j,word in enumerate([ones]+axes):
            residue=reduce_vector(word,space)[0]
            residue,coef=reduce_vector(residue,affine)
            coef^=1<<j
            if residue:
                affine[residue.bit_length()-1]=residue,coef
            else:
                equations.append((coef>>1,coef&1))
        flat=affine_domain(N,equations)
        if flat is None:
            return 'NO',None,trace
        point,steps,_=flat
        if len(steps)<N:
            origin^=apply_basis(dirs,point)
            dirs=[apply_basis(dirs,d) for d in steps]
            H.clear()
            continue
        literals=[w for a in axes for w in (ones^a,a)]
        added={(a,b) for a,b in combinations(range(2*N),2) if a//2!=b//2 and (a,b) not in H
               and not reduce_vector(literals[a]&literals[b],space)[0]}
        if not added:
            return 'UNKNOWN',None,trace
        H.update(added)
