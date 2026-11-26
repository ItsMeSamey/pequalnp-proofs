"""Necessary local profile census for a hypothetical seven-product list."""
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'g3-complex-conic-search'))
from search import stabs, orbit_reps, unit
p=65537
inv=np.array([0]+[pow(i,-1,p) for i in range(1,p)],dtype=np.int64)
def quotient(matrix,row):
    k=np.flatnonzero(row)[0]
    residual=(matrix-matrix[:,k,None]*row*inv[row[k]])%p
    v=residual[np.arange(len(matrix)),np.argmax(residual!=0,axis=1)]
    return residual*inv[v,None]%p
def groups(matrix):
    out={}
    for i,row in enumerate(matrix):out.setdefault(row.tobytes(),[]).append(i)
    return list(out.values())
def census():
    phases=stabs()
    A=np.array([[0 if v<0 else unit[v] for v in row] for row in phases],dtype=np.int64)
    g=np.array([1]*7+[p-1],dtype=np.int64)
    Q=quotient(A,g)
    maxline=max(map(len,groups(Q)))
    assert len(A)==1080 and maxline<=2
    planes=set()
    for i,_ in orbit_reps(phases):
        M=quotient(Q,Q[i])
        base=np.where(~M.any(axis=1))[0].tolist()
        for J in groups(M):
            if J[0] in base:continue
            ids=tuple(sorted(base+J))
            if len(ids)>=5:planes.add(ids)
    profiles=Counter()
    for ids in planes:
        F=A[list(ids)]
        m=len(ids)
        lines=set()
        for i in range(m):
            N=quotient(np.vstack((F,g)),F[i])
            for J in groups(N):
                if i not in J and m not in J:
                    lines.add(tuple(sorted([i]+J)))
        for k in range(5,min(m,7)+1):
            for distinct in combinations(range(m),k):
                for repeated in combinations(distinct,7-k):
                    weights=[int(j in distinct)+int(j in repeated) for j in range(m)]
                    if not any(sum(weights[j] for j in line)>=4 for line in lines):
                        profiles[(m,k)]+=1
    print({'rays':len(A),'maxline':maxline,'plane_reps_with_redundancy':dict(Counter(map(len,planes))),'viable_multisets':dict(profiles)},flush=True)
if __name__=='__main__':census()
