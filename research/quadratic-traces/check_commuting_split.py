"""Independent finite-field witness search via cyclic subspaces, including GF(4)."""
from itertools import product
from random import Random
rng=Random(35276)

class Field:
    def __init__(self,q): self.q=q
    def add(self,a,b): return a^b if self.q==4 else (a+b)%self.q
    def mul(self,a,b):
        if self.q!=4: return (a*b)%self.q
        v=(a if b&1 else 0)^((a<<1) if b&2 else 0)
        return v^7 if v&4 else v
    def neg(self,a): return a if self.q==4 else (-a)%self.q
    def dot(self,x,y):
        v=0
        for a,b in zip(x,y): v=self.add(v,self.mul(a,b))
        return v
    def mv(self,A,x): return tuple(self.dot(r,x) for r in A)
    def basis(self,vec):
        piv={}; basis=[]
        for raw in vec:
            v=list(raw)
            for j,w in sorted(piv.items()):
                c=self.neg(v[j])
                if c: v=[self.add(a,self.mul(c,b)) for a,b in zip(v,w)]
            if not any(v): continue
            j=next(i for i,a in enumerate(v) if a)
            inv=next(s for s in range(1,self.q) if self.mul(s,v[j])==1)
            piv[j]=[self.mul(inv,a) for a in v];basis.append(raw)
        return basis

def independent_search(F,A,T):
    n=len(A); H=[]
    def isotropic(L): return all(F.dot(F.mv(A,v),w)==0 for v in L for w in L)
    # This exhaustive oracle is intentionally independent of the proof's linearized solver.
    while 2*len(H)<n:
        for v in product(range(F.q),repeat=n):
            L=F.basis(H+[v])
            if len(L)==len(H): continue
            while True:
                D=F.basis(L+[F.mv(M,w) for M in T for w in L])
                if len(D)==len(L): break
                L=D
            if isotropic(L):
                H=L
                break
        else: raise AssertionError("no invariant isotropic extension")
    assert len(H)*2==n and isotropic(H)
    assert len(F.basis(H+[F.mv(M,w) for M in T for w in H]))==len(H)
    return H

def mats(n): return [[0]*n for _ in range(n)]
if __name__ == "__main__":
    cases=0
    for q in (2,3,4,5):
        F=Field(q)
        for d in (2,3):
            A=mats(2*d)
            for i in range(d): A[i][i+d]=1;A[i+d][i]=F.neg(1)
            for _ in range(5):
                # Upper-triangular first-block generators, transpose second-block action.
                T=[]
                for j in range(3):
                    S=mats(2*d)
                    for i in range(d):
                        for k in range(i,d):
                            S[i][k]=S[k+d][i+d]=rng.randrange(q)
                    T.append(S)
                independent_search(F,A,T); cases+=1
        if q in (2,4):
            A=mats(4); U=mats(4);V=mats(4)
            for j in range(4):
                A[j][3-j]=1
                if not j&1: U[j|1][j]=1
                if not j&2: V[j|2][j]=1
            independent_search(F,A,[U,V])
            e=(1,0,0,0)
            assert F.dot(F.mv(A,e),F.mv(U,F.mv(V,e)))==1
            cases+=1
    print(f"{cases} invariant Lagrangian witnesses over GF(2), GF(3), GF(4), GF(5); product-test counterexamples checked")
