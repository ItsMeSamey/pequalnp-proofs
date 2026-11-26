"""Polynomial finite-field construction by lifting through H-perp/H."""
from check_commuting_split import Field,mats
from random import Random

def null(F,rows,n):
    rows=[list(v) for v in rows]; piv=[]; i=0
    for j in range(n):
        k=next((k for k in range(i,len(rows)) if rows[k][j]),None)
        if k is None: continue
        rows[i],rows[k]=rows[k],rows[i]
        inv=next(s for s in range(1,F.q) if F.mul(s,rows[i][j])==1)
        rows[i]=[F.mul(a,inv) for a in rows[i]]
        for l in range(len(rows)):
            if l==i: continue
            z=F.neg(rows[l][j])
            if z: rows[l]=[F.add(a,F.mul(z,b)) for a,b in zip(rows[l],rows[i])]
        piv.append(j);i+=1
    result=[]
    for free in range(n):
        if free in piv: continue
        vec=[0]*n;vec[free]=1
        for i,j in enumerate(piv): vec[j]=F.neg(rows[i][free])
        result.append(tuple(vec))
    return result

def mm(F,P,Q):
    return [tuple(F.dot(r,c) for c in zip(*Q)) for r in P]

def construct(F,A,T):
    n=len(A)
    identity=[tuple(int(i==j) for j in range(n)) for i in range(n)]
    algebra=[identity]
    while True:
        gen=algebra+[mm(F,S,M) for S in T for M in algebra]
        flat=F.basis([tuple(k for row in X for k in row) for X in gen])
        if len(flat)==len(algebra): break
        algebra=[[f[i*n:(i+1)*n] for i in range(n)] for f in flat]
    comm=[]
    for j,S in enumerate(T):
        for R in T[:j]:
            X,Y=mm(F,S,R),mm(F,R,S)
            C=[tuple(F.add(u,F.neg(v)) for u,v in zip(a,b)) for a,b in zip(X,Y)]
            if any(any(r) for r in C): comm.append(C)
    H=[]
    while 2*len(H)<n:
        perp=null(F,[F.mv(A,h) for h in H],n)
        equations=[F.mv(A,h) for h in H]
        # Force [S,T] M x in H for all algebra basis M, by testing against H-perp.
        cov=[F.mv(A,w) for w in perp]
        for C in comm:
            for M in algebra:
                D=mm(F,C,M)
                equations += [tuple(F.dot(a,b) for b in zip(*D)) for a in cov]
        W=null(F,equations,n)
        if F.q in (2,4):
            good=[]
            for M in algebra:
                diag=[F.dot(F.mv(A,w),F.mv(M,w)) for w in W]
                good.append([next(z for z in range(F.q) if F.mul(z,z)==d) for d in diag])
            coeffs=null(F,good,len(W))
            W=[tuple(F.dot(z,c) for c in zip(*W)) for z in coeffs]
        v=next((w for w in W if len(F.basis(H+[w]))>len(H)),None)
        if v is None: raise ValueError("commutative-annihilator recursion stalled")
        H=F.basis(H+[F.mv(M,v) for M in algebra])
    assert len(H)*2==n
    assert all(F.dot(F.mv(A,u),v)==0 for u in H for v in H)
    assert len(F.basis(H+[F.mv(S,u) for S in T for u in H]))==len(H)
    return H

if __name__=="__main__":
    rng=Random(537)
    count=0
    for q in (2,3,4,5):
        F=Field(q)
        for d in (2,3):
            A=mats(2*d)
            for j in range(d): A[j][d+j]=1;A[d+j][j]=F.neg(1)
            for _ in range(5):
                T=[]
                for i in range(2):
                    M=mats(2*d)
                    for j in range(d):
                        for k in range(j,d):
                            M[j][k]=M[d+k][d+j]=rng.randrange(q)
                    T.append(M)
                construct(F,A,T);count+=1
    print(f"Polynomial module algorithm constructed and checked {count} Lagrangians")
