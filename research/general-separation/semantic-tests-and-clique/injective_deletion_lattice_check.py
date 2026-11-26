"""Integer elementary column operations for common ordered deletion marginals."""
from itertools import permutations
from math import gcd
import numpy as np

def solve(r,h):
    words=list(permutations(range(h),r))
    sub=list(permutations(range(h),r-1))
    rows=[(d,v) for d in range(1,r) for v in sub]
    a=np.zeros((len(rows)+1,len(words)),dtype=object)
    for j,w in enumerate(words):
        for d in range(1,r):
            a[rows.index((d,w[:d]+w[d+1:])),j]+=1
            a[rows.index((d,w[1:])),j]-=1
    a[-1,:]=1
    original=a.copy()
    trans=np.identity(len(words),dtype=object)
    k=0
    for i in range(len(rows)+1):
        nz=[j for j in range(k,len(words)) if a[i,j]]
        if not nz:
            continue
        p=min(nz,key=lambda j:abs(a[i,j]))
        if k!=p:
            a[:,[k,p]]=a[:,[p,k]]
            trans[:,[k,p]]=trans[:,[p,k]]
        for j in nz:
            if j==k:continue
            while a[i,j]:
                q=a[i,k]//a[i,j]
                if q:
                    a[:,k]-=q*a[:,j]
                    trans[:,k]-=q*trans[:,j]
                a[:,[k,j]]=a[:,[j,k]]
                trans[:,[k,j]]=trans[:,[j,k]]
        if i==len(rows):
            val=int(a[i,k])
            sol=trans[:,k]*(1 if val>0 else -1)
            assert list(original@sol)==[0]*len(rows)+[abs(val)]
            return abs(val),[(w,c) for w,c in zip(words,sol) if c]
        k+=1
if __name__=='__main__':
    for r,h in ((3,4),(4,5),(4,6)):
        mass,solution=solve(r,h)
        print(r,h,mass,len(solution),max(abs(v) for _,v in solution),flush=True)
        if r==3: print(solution,flush=True)

def dual(r,h,p):
    sub=list(permutations(range(h),r-1))
    m=(r-1)*len(sub)
    rows=[]
    for w in permutations(range(h),r):
        row=[0]*(m+1)
        for d in range(1,r):
            off=(d-1)*len(sub)
            row[off+sub.index(w[:d]+w[d+1:])]+=1
            row[off+sub.index(w[1:])]-=1
        row[-1]=1
        rows.append(row)
    a=np.array(rows,dtype=int)%p
    src=a.copy()
    k=0
    piv=[]
    for j in range(m):
        hits=np.flatnonzero(a[k:,j])
        if not len(hits):continue
        i=k+hits[0]
        a[[k,i]]=a[[i,k]]
        a[k]=a[k]*pow(int(a[k,j]),-1,p)%p
        for i in range(len(a)):
            if i!=k and a[i,j]:
                a[i]=(a[i]-a[i,j]*a[k])%p
        piv.append(j)
        k+=1
    sol=np.zeros(m,dtype=int)
    sol[piv]=a[:k,-1]
    assert np.all((src[:,:m]@sol)%p==1)
    return [list(map(int,row)) for row in sol.reshape(r-1,-1)]
if __name__=='__main__':
    for r,h,p in ((3,4,3),(4,5,2),(4,5,3),(4,6,2)):
        v=dual(r,h,p)
        print('dual',r,h,p, v if r==3 else 'verified')
